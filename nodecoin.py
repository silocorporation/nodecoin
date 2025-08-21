#!/usr/bin/env python3
"""
simplecoin_auto_keys_zmq.py

- Auto-generate libzmq CURVE keypairs for node (if missing) and save them.
- Node autostarts PUB/SUB/REP and auto-connects to provided peer PUB endpoints.
- Wallet (GTK) auto-generates its own CURVE client keypair and its ECDSA spending key on first run.
- Communication uses ZeroMQ CURVE (encrypted & authenticated).
- Simplified educational chain (P2PKH-like, ECDSA per-input signatures, UTXO verification).
"""

import os, sys, time, json, hashlib, threading, sqlite3, math
from dataclasses import dataclass, asdict
from typing import List, Optional
import zmq
from ecdsa import SigningKey, VerifyingKey, SECP256k1, BadSignatureError

# ----------------------
# Config (kept small)
# ----------------------
COIN = 10**8
DEFAULT_TARGET = 2**250
DB_TEMPLATE = "simplecoin_auto_{network}_{port}.db"

# ----------------------
# Utilities
# ----------------------
def sha256(b: bytes) -> bytes:
    import hashlib
    return hashlib.sha256(b).digest()

def pubkey_to_address(pub: bytes) -> str:
    h = hashlib.sha256(pub).digest()
    rip = hashlib.new("ripemd160", h).digest()
    return rip.hex()

def write_file_if_missing(path: str, data: bytes):
    if not os.path.exists(path):
        with open(path, "wb") as f:
            f.write(data)
        return True
    return False

def load_keyfile(path: str) -> bytes:
    with open(path, "rb") as f:
        return f.read().strip()

# ----------------------
# CURVE helpers
# ----------------------
def generate_curve_keypair_bytes():
    # returns (pub_bytes, priv_bytes)
    return zmq.curve_keypair()

def ensure_curve_keypair(prefix: str):
    """
    Ensure files <prefix>_curve_pub.key and <prefix>_curve_priv.key exist.
    If not, generate and write them.
    Returns (pub_bytes, priv_bytes, pub_path, priv_path, created_flag)
    """
    pub_path = f"{prefix}_curve_pub.key"
    priv_path = f"{prefix}_curve_priv.key"
    created = False
    if not (os.path.exists(pub_path) and os.path.exists(priv_path)):
        pub, priv = generate_curve_keypair_bytes()
        with open(pub_path, "wb") as f: f.write(pub)
        with open(priv_path, "wb") as f: f.write(priv)
        created = True
        print(f"[keys] Generated CURVE keypair: {pub_path}, {priv_path}")
    else:
        pub = load_keyfile(pub_path)
        priv = load_keyfile(priv_path)
    return pub, priv, pub_path, priv_path, created

# ----------------------
# Minimal TX/UTXO dataclasses
# ----------------------
@dataclass
class TXOutput:
    value: int
    address: str

@dataclass
class TXInput:
    prev_txid: str
    prev_index: int
    signature: Optional[str] = None  # "<sig_hex>:<pub_hex>"

@dataclass
class Transaction:
    txid: str
    inputs: List[TXInput]
    outputs: List[TXOutput]
    def to_json(self):
        return json.dumps({"txid": self.txid, "inputs":[asdict(i) for i in self.inputs], "outputs":[asdict(o) for o in self.outputs]}, sort_keys=True)
    @staticmethod
    def from_json(s: str):
        j = json.loads(s)
        ins = [TXInput(**i) for i in j["inputs"]]
        outs = [TXOutput(**o) for o in j["outputs"]]
        return Transaction(txid=j["txid"], inputs=ins, outputs=outs)

def input_sighash(inputs: List[TXInput], outputs: List[TXOutput], idx: int) -> bytes:
    in_repr = [{"prev_txid": i.prev_txid, "prev_index": i.prev_index} for i in inputs]
    out_repr = [asdict(o) for o in outputs]
    payload = {"inputs": in_repr, "outputs": out_repr, "index": idx}
    return sha256(json.dumps(payload, sort_keys=True).encode())

def compute_txid(inputs: List[TXInput], outputs: List[TXOutput]) -> str:
    s = json.dumps({"inputs":[asdict(i) for i in inputs], "outputs":[asdict(o) for o in outputs]}, sort_keys=True).encode()
    return sha256(s).hex()

# ----------------------
# Very small NodeChain (sqlite-backed, no heavy reorg logic here)
# ----------------------
class NodeChain:
    def __init__(self, network: str, port: int):
        self.network = network
        self.port = port
        self.db = DB_TEMPLATE.format(network=network, port=port)
        self.conn = sqlite3.connect(self.db, check_same_thread=False)
        self._init_db()
        # ensure genesis
        if self.get_chain_height() == 0:
            self._create_genesis()
        self.lock = threading.Lock()

    def _init_db(self):
        c = self.conn.cursor()
        c.execute("CREATE TABLE IF NOT EXISTS blocks (height INTEGER PRIMARY KEY, hash TEXT, prev_hash TEXT, timestamp INTEGER, nonce INTEGER, txs TEXT)")
        c.execute("CREATE TABLE IF NOT EXISTS utxos (txid TEXT, idx INTEGER, value INTEGER, address TEXT, spent INTEGER DEFAULT 0, PRIMARY KEY(txid, idx))")
        c.execute("CREATE TABLE IF NOT EXISTS mempool (txid TEXT PRIMARY KEY, tx TEXT)")
        self.conn.commit()

    def _create_genesis(self):
        c = self.conn.cursor()
        c.execute("INSERT OR IGNORE INTO blocks (height, hash, prev_hash, timestamp, nonce, txs) VALUES (?,?,?,?,?,?)",
                  (0, "0"*64, "", int(time.time()), 0, json.dumps([])))
        self.conn.commit()

    def get_chain_height(self):
        c = self.conn.cursor()
        c.execute("SELECT MAX(height) FROM blocks")
        r = c.fetchone()[0]
        return int(r) if r is not None else 0

    def get_tip(self):
        h = self.get_chain_height()
        c = self.conn.cursor()
        c.execute("SELECT hash FROM blocks WHERE height = ?", (h,))
        r = c.fetchone()
        return h, (r[0] if r else "0"*64)

    def add_tx_to_mempool(self, tx: Transaction) -> bool:
        with self.lock:
            if not self.verify_tx(tx, allow_coinbase=False):
                return False
            c = self.conn.cursor()
            c.execute("INSERT OR REPLACE INTO mempool (txid, tx) VALUES (?,?)", (tx.txid, tx.to_json()))
            self.conn.commit()
            return True

    def get_mempool(self):
        c = self.conn.cursor()
        c.execute("SELECT tx FROM mempool")
        return [Transaction.from_json(r[0]) for r in c.fetchall()]

    def clear_mempool(self):
        c = self.conn.cursor()
        c.execute("DELETE FROM mempool")
        self.conn.commit()

    def verify_tx(self, tx: Transaction, allow_coinbase: bool=False) -> bool:
        # coinbase check
        if len(tx.inputs) == 0:
            return allow_coinbase
        c = self.conn.cursor()
        total_in = 0
        for i, vin in enumerate(tx.inputs):
            c.execute("SELECT txid, idx, value, address, spent FROM utxos WHERE txid=? AND idx=?", (vin.prev_txid, vin.prev_index))
            r = c.fetchone()
            if not r:
                return False
            _txid, _idx, value, address, spent = r
            if spent:
                return False
            total_in += value
            if not vin.signature:
                return False
            try:
                sig_hex, pub_hex = vin.signature.split(":")
                pub_bytes = bytes.fromhex(pub_hex)
            except Exception:
                return False
            if pubkey_to_address(pub_bytes) != address:
                return False
            digest = input_sighash(tx.inputs, tx.outputs, i)
            try:
                vk = VerifyingKey.from_string(pub_bytes, curve=SECP256k1)
                vk.verify(bytes.fromhex(sig_hex), digest)
            except Exception:
                return False
        total_out = sum(o.value for o in tx.outputs)
        if total_in < total_out:
            return False
        return True

    def add_block(self, prev_hash: str, nonce: int, txs: List[Transaction], timestamp: Optional[int]=None):
        if timestamp is None:
            timestamp = int(time.time())
        with self.lock:
            height = self.get_chain_height() + 1
            txs_json = json.dumps([t.to_json() for t in txs])
            header = f"{height}{prev_hash}{timestamp}{nonce}{txs_json}".encode()
            block_hash = sha256(header).hex()
            c = self.conn.cursor()
            c.execute("INSERT INTO blocks (height, hash, prev_hash, timestamp, nonce, txs) VALUES (?,?,?,?,?,?)",
                      (height, block_hash, prev_hash, timestamp, nonce, txs_json))
            # update utxos: mark inputs spent and add outputs
            for t in txs:
                for vin in t.inputs:
                    c.execute("UPDATE utxos SET spent = 1 WHERE txid = ? AND idx = ?", (vin.prev_txid, vin.prev_index))
                for idx, out in enumerate(t.outputs):
                    c.execute("INSERT OR REPLACE INTO utxos (txid, idx, value, address, spent) VALUES (?,?,?,?,0)",
                              (t.txid, idx, out.value, out.address))
            self.conn.commit()
            return height, block_hash

    def utxos_for_address(self, address: str):
        c = self.conn.cursor()
        c.execute("SELECT txid, idx, value FROM utxos WHERE address = ? AND spent = 0", (address,))
        return c.fetchall()

# ----------------------
# ZMQ Node with CURVE auto keys + auto-start
# ----------------------
class AutoZMQNode:
    def __init__(self, network: str, port: int, pub_bind: str, rpc_bind: str, peers: List[str], key_prefix: str):
        self.network = network
        self.port = port
        self.pub_bind = pub_bind
        self.rpc_bind = rpc_bind
        self.peers = peers
        self.key_prefix = key_prefix

        # ensure node CURVE keypair exists (auto-generate if missing)
        self.server_pub, self.server_priv, self.pub_path, self.priv_path, created = ensure_curve_keypair(self.key_prefix)
        if created:
            print(f"[node] Auto-generated CURVE keys for node: {self.pub_path} , {self.priv_path}")

        # zmq context and sockets
        self.ctx = zmq.Context.instance()
        # PUB (bind) - server keys required
        self.pub = self.ctx.socket(zmq.PUB)
        self.pub.curve_publickey = self.server_pub
        self.pub.curve_secretkey = self.server_priv
        self.pub.bind(self.pub_bind)

        # SUB (connect to peers) - client keypair required for CURVE auth when connecting to servers.
        # For node-to-node we reuse node's own keys as client credentials (convenient).
        self.sub = self.ctx.socket(zmq.SUB)
        self.sub.curve_publickey = self.server_pub
        self.sub.curve_secretkey = self.server_priv
        self.sub.setsockopt(zmq.SUBSCRIBE, (self.network + "|").encode())
        for p in self.peers:
            # when connecting we should set curve_serverkey for each peer to their public key
            # For the demo we assume peers are open or keys are known. We'll just connect.
            try:
                self.sub.connect(p)
                print(f"[node] SUB connected to {p}")
            except Exception as e:
                print("[node] SUB connect failed", e)

        # REP RPC (bind) - server keys on REP as well
        self.rep = self.ctx.socket(zmq.REP)
        self.rep.curve_publickey = self.server_pub
        self.rep.curve_secretkey = self.server_priv
        self.rep.bind(self.rpc_bind)

        # chain
        self.chain = NodeChain(network=self.network, port=self.port)

        # runtime
        self.running = False
        self.threads = []

    def start(self):
        self.running = True
        t_sub = threading.Thread(target=self._sub_loop, daemon=True)
        t_sub.start()
        self.threads.append(t_sub)
        t_rep = threading.Thread(target=self._rep_loop, daemon=True)
        t_rep.start()
        self.threads.append(t_rep)
        print(f"[node] Node started. PUB {self.pub_bind}  RPC {self.rpc_bind}")
        # immediately attempt to connect to peers (done above during connect)
        # optional: start a periodic status print
        t_status = threading.Thread(target=self._status_loop, daemon=True); t_status.start(); self.threads.append(t_status)

    def _status_loop(self):
        while self.running:
            time.sleep(10)
            h, tip = self.chain.get_tip()
            print(f"[node status] height={h} tip={tip[:12]} mempool={len(self.chain.get_mempool())}")

    def _sub_loop(self):
        poll = zmq.Poller()
        poll.register(self.sub, zmq.POLLIN)
        while self.running:
            socks = dict(poll.poll(300))
            if self.sub in socks and socks[self.sub] == zmq.POLLIN:
                raw = self.sub.recv()
                try:
                    data = raw[len((self.network + "|").encode()):]
                    obj = json.loads(data.decode())
                    self._handle_gossip(obj)
                except Exception as e:
                    print("[sub] decode error", e)

    def _handle_gossip(self, obj):
        typ = obj.get("type")
        payload = obj.get("payload")
        if typ == "tx":
            try:
                tx = Transaction.from_json(payload)
                ok = self.chain.add_tx_to_mempool(tx)
                if ok:
                    print(f"[gossip] accepted tx {tx.txid[:12]}")
            except Exception as e:
                print("[gossip] tx error", e)
        elif typ == "block":
            try:
                block = payload
                txs = [Transaction.from_json(tj) for tj in block.get("txs", [])]
                prev_hash = block.get("prev_hash")
                nonce = block.get("nonce")
                ts = block.get("timestamp")
                h, bhash = self.chain.add_block(prev_hash=prev_hash, nonce=nonce, txs=txs, timestamp=ts)
                print(f"[gossip] added block height {h}")
                self.chain.clear_mempool()
            except Exception as e:
                print("[gossip] block error", e)

    def _rep_loop(self):
        while self.running:
            try:
                msg = self.rep.recv_json(flags=0)
            except Exception:
                continue
            typ = msg.get("type")
            payload = msg.get("payload")
            if typ == "submit_tx":
                try:
                    tx = Transaction.from_json(payload)
                    ok = self.chain.add_tx_to_mempool(tx)
                    if ok:
                        # broadcast locally
                        self._publish({"type":"tx", "payload": tx.to_json()})
                    self.rep.send_json({"type":"ack","payload":{"accepted":ok,"txid":tx.txid}})
                except Exception as e:
                    self.rep.send_json({"type":"error","payload":{"msg":str(e)}})
            elif typ == "get_utxos":
                addr = payload.get("address")
                utx = [{"txid":txid,"idx":idx,"value":value} for (txid, idx, value) in self.chain.utxos_for_address(addr)]
                self.rep.send_json({"type":"utxos","payload":utx})
            elif typ == "get_tip":
                h, tip = self.chain.get_tip()
                self.rep.send_json({"type":"tip","payload":{"height":h,"tip":tip}})
            elif typ == "publish_block":
                try:
                    blk = payload
                    txs = [Transaction.from_json(tj) for tj in blk.get("txs",[])]
                    h,bhash = self.chain.add_block(prev_hash=blk.get("prev_hash"), nonce=blk.get("nonce"), txs=txs, timestamp=blk.get("timestamp"))
                    self.chain.clear_mempool()
                    self._publish({"type":"block","payload":blk})
                    self.rep.send_json({"type":"ack","payload":{"accepted":True,"height":h}})
                except Exception as e:
                    self.rep.send_json({"type":"ack","payload":{"accepted":False,"error":str(e)}})
            else:
                self.rep.send_json({"type":"error","payload":{"msg":"unknown"}})

    def _publish(self, obj: dict):
        payload = self.network + "|" + json.dumps(obj)
        try:
            self.pub.send_string(payload)
        except Exception as e:
            print("[publish] error", e)

    def stop(self):
        self.running = False
        time.sleep(0.2)
        try:
            self.pub.close(); self.sub.close(); self.rep.close(); self.ctx.term()
        except:
            pass

# ----------------------
# GTK Wallet (auto-generate its own keys on first run)
# ----------------------
try:
    import gi
    gi.require_version("Gtk", "3.0")
    from gi.repository import Gtk, GLib
    GUI_AVAILABLE = True
except Exception:
    GUI_AVAILABLE = False

class AutoWalletGTK:
    def __init__(self, rpc_addr: str, client_key_prefix: str = "wallet"):
        if not GUI_AVAILABLE:
            raise RuntimeError("GTK not available")
        self.rpc_addr = rpc_addr
        # ensure client CURVE keypair exists
        self.client_pub, self.client_priv, self.client_pub_path, self.client_priv_path, created = ensure_curve_keypair(client_key_prefix)
        if created:
            print(f"[wallet] generated client CURVE keys {self.client_pub_path} {self.client_priv_path}")
        # ensure an ECDSA spending key exists
        self.wallet_sk_path = f"{client_key_prefix}_ecdsa_sk.hex"
        if not os.path.exists(self.wallet_sk_path):
            sk = SigningKey.generate(curve=SECP256k1)
            with open(self.wallet_sk_path, "w") as f:
                f.write(sk.to_string().hex())
            print(f"[wallet] generated ECDSA spending key {self.wallet_sk_path}")
            self.sk = sk
        else:
            with open(self.wallet_sk_path, "r") as f:
                hexs = f.read().strip()
                self.sk = SigningKey.from_string(bytes.fromhex(hexs), curve=SECP256k1)
        self.pubkey_bytes = self.sk.get_verifying_key().to_string()
        self.address = pubkey_to_address(self.pubkey_bytes)

        # prepare ZMQ REQ with CURVE auth
        self.ctx = zmq.Context.instance()
        self.req = self.ctx.socket(zmq.REQ)
        self.req.curve_publickey = self.client_pub
        self.req.curve_secretkey = self.client_priv
        # node RPC server pubkey must be provided by user RPC server; for simplicity in demo we do not set curve_serverkey
        # but setting it is recommended if you know server pubkey beforehand (req.curve_serverkey = server_pub_bytes)
        self.req.connect(self.rpc_addr)

        # GTK UI
        self.win = Gtk.Window(title="SimpleCoin AutoWallet")
        self.win.set_default_size(640, 360)
        self.win.connect("destroy", lambda w: Gtk.main_quit())
        v = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6); v.set_margin_top(6); v.set_margin_bottom(6); v.set_margin_start(6); v.set_margin_end(6)
        self.win.add(v)
        self.addr_label = Gtk.Label(label=f"Address: {self.address}")
        v.pack_start(self.addr_label, False, False, 0)
        self.balance_label = Gtk.Label(label="Balance: 0")
        v.pack_start(self.balance_label, False, False, 0)
        frm = Gtk.Frame(label="Send"); v.pack_start(frm, False, False, 0)
        sendbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4); sendbox.set_margin_top(6); sendbox.set_margin_bottom(6); sendbox.set_margin_start(6); sendbox.set_margin_end(6)
        self.to_entry = Gtk.Entry(); self.to_entry.set_placeholder_text("Destination address"); sendbox.pack_start(self.to_entry, False, False, 0)
        self.amount_entry = Gtk.Entry(); self.amount_entry.set_placeholder_text("Amount (coins)"); sendbox.pack_start(self.amount_entry, False, False, 0)
        send_btn = Gtk.Button(label="Create & Submit TX"); send_btn.connect("clicked", self.on_send); sendbox.pack_start(send_btn, False, False, 0)
        frm.add(sendbox)
        self.status = Gtk.Statusbar(); v.pack_start(self.status, False, False, 0)
        self.win.show_all()
        GLib.timeout_add_seconds(3, self._periodic_refresh)

    def _push(self, s: str):
        self.status.push(0, s)

    def rpc_call(self, obj: dict):
        try:
            self.req.send_json(obj)
            resp = self.req.recv_json()
            return resp
        except Exception as e:
            return {"type":"error","payload":{"msg":str(e)}}

    def update_balance(self):
        resp = self.rpc_call({"type":"get_utxos","payload":{"address":self.address}})
        if resp and resp.get("type")=="utxos":
            ut = resp.get("payload", [])
            bal = sum(x.get("value",0) for x in ut)
            self.balance_label.set_text(f"Balance: {bal/COIN:.8f}")
        else:
            self._push("RPC error fetching utxos")

    def on_send(self, widget):
        to = self.to_entry.get_text().strip()
        try:
            amount = float(self.amount_entry.get_text().strip())
        except:
            self._push("Invalid amount")
            return
        amt_units = int(math.floor(amount * COIN))
        # get utxos
        resp = self.rpc_call({"type":"get_utxos","payload":{"address":self.address}})
        if not resp or resp.get("type")!="utxos":
            self._push("RPC error")
            return
        utxos = resp.get("payload", [])
        if not utxos:
            self._push("No funds")
            return
        selected = []; total = 0
        for u in utxos:
            selected.append((u["txid"], u["idx"], u["value"])); total += u["value"]
            if total >= amt_units: break
        if total < amt_units:
            self._push("Insufficient funds")
            return
        inputs = [TXInput(prev_txid=txid, prev_index=idx, signature=None) for (txid, idx, _v) in selected]
        outputs = [TXOutput(value=amt_units, address=to)]
        change = total - amt_units
        if change > 0:
            outputs.append(TXOutput(value=change, address=self.address))
        # per-input sign
        for i in range(len(inputs)):
            digest = input_sighash(inputs, outputs, i)
            sig = self.sk.sign_deterministic(digest)
            inputs[i].signature = f"{sig.hex()}:{self.sk.get_verifying_key().to_string().hex()}"
        txid = compute_txid(inputs, outputs)
        tx = Transaction(txid=txid, inputs=inputs, outputs=outputs)
        resp = self.rpc_call({"type":"submit_tx","payload":tx.to_json()})
        if resp and resp.get("type")=="ack" and resp.get("payload",{}).get("accepted"):
            self._push("TX accepted by node")
        else:
            self._push("Node rejected tx or RPC error")
        self.update_balance()

    def _periodic_refresh(self):
        self.update_balance()
        return True

# ----------------------
# CLI runner
# ----------------------
def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--node", action="store_true")
    p.add_argument("--wallet", action="store_true")
    p.add_argument("--network", default="testnet")
    p.add_argument("--port", type=int, default=30001)
    p.add_argument("--pub-bind", default="tcp://*:30001")
    p.add_argument("--rpc-bind", default="tcp://*:30002")
    p.add_argument("--peers", default="", help="comma-separated PUB endpoints (tcp://host:port)")
    p.add_argument("--key-prefix", default="node", help="prefix for node CURVE key files (auto-generated if missing)")
    p.add_argument("--rpc-connect", default="tcp://localhost:30002", help="wallet connects to node RPC here")
    p.add_argument("--wallet-prefix", default="wallet", help="prefix for wallet keys (client curve + ecdsa sk)")
    args = p.parse_args()

    if args.node:
        peers = [x.strip() for x in args.peers.split(",") if x.strip()]
        node = AutoZMQNode(network=args.network, port=args.port, pub_bind=args.pub_bind, rpc_bind=args.rpc_bind, peers=peers, key_prefix=args.key_prefix)
        node.start()
        # optionl: auto-mine if you want (omitted here)
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            print("shutting down")
            node.stop()

    elif args.wallet:
        if not GUI_AVAILABLE:
            print("GTK not available. Install python3-gi.")
            return
        wallet = AutoWalletGTK(rpc_addr=args.rpc_connect, client_key_prefix=args.wallet_prefix)
        Gtk.main()
    else:
        print("Run with --node or --wallet. Example:")
        print("  python3 simplecoin_auto_keys_zmq.py --node --pub-bind tcp://*:30001 --rpc-bind tcp://*:30002 --peers tcp://localhost:31001 --key-prefix nodeA")
        print("  python3 simplecoin_auto_keys_zmq.py --wallet --rpc-connect tcp://localhost:30002 --wallet-prefix wallet1")

if __name__ == "__main__":
    main()
