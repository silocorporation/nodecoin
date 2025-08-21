#!/usr/bin/env python3
"""
simplecoin_secure_zmq.py

Educational decentralized cryptocurrency with:
- per-input ECDSA signatures (secp256k1) (P2PKH-like)
- UTXO verification
- ZeroMQ PUB/SUB decentralized gossip with CURVE (libzmq) auth
- ZeroMQ REP RPC for wallet <-> node
- Header-first processing + simple reorg handling (rebuild UTXO set on switch to longer chain)

Usage examples (after generating keys; see generate_curve_keys() below):

# Node A
python3 simplecoin_secure_zmq.py --node --network testnet \
  --pub-bind tcp://*:30001 --rpc-bind tcp://*:30002 \
  --pub-key-file nodeA_pub.key --priv-key-file nodeA_priv.key \
  --peer-pubs tcp://localhost:31001

# Node B (different port & keys)
python3 simplecoin_secure_zmq.py --node --network testnet \
  --pub-bind tcp://*:31001 --rpc-bind tcp://*:31002 \
  --pub-key-file nodeB_pub.key --priv-key-file nodeB_priv.key \
  --peer-pubs tcp://localhost:30001

# Wallet (client) using its own CURVE key connecting to Node A RPC
python3 simplecoin_secure_zmq.py --wallet --rpc-connect tcp://localhost:30002 \
  --client-pub client_pub.key --client-priv client_priv.key

Notes:
- You must generate server keypair (node) and client keypairs (wallet) with generate_curve_keypair() helper before running.
- CURVE: Publisher/REP binds must set server keys; SUB/REQ sockets must set client keypair and set CURVE_SERVERKEY to server pubkey when connecting.
"""

import argparse, os, sys, time, json, hashlib, threading, sqlite3
import math
from dataclasses import dataclass, asdict
from typing import List, Optional, Tuple
import zmq

# cryptography for ECDSA
from ecdsa import SigningKey, VerifyingKey, SECP256k1, BadSignatureError

# -------------------------
# ECONOMICS / CONFIG
# -------------------------
TOTAL_COINS = 24_000_000
YEARS = 700
BLOCK_TIME_SECONDS = 10 * 60
COIN = 10**8

BLOCKS_IN_EMISSION = int((YEARS * 365.25 * 24 * 3600) // BLOCK_TIME_SECONDS)
REWARD_PER_BLOCK_UNITS = (TOTAL_COINS * COIN) // BLOCKS_IN_EMISSION
REWARD_REMAINDER_UNITS = (TOTAL_COINS * COIN) - (REWARD_PER_BLOCK_UNITS * BLOCKS_IN_EMISSION)

DEFAULT_TARGET = 2**250  # easyish for local CPU
DB_TEMPLATE = "simplecoin_secure_{network}_{port}.db"

# -------------------------
# Utilities
# -------------------------
def sha256(b: bytes) -> bytes:
    import hashlib
    return hashlib.sha256(b).digest()

def sha256_hex(b: bytes) -> str:
    import hashlib
    return hashlib.sha256(b).hexdigest()

def pubkey_to_address(pub: bytes) -> str:
    h = hashlib.sha256(pub).digest()
    rip = hashlib.new("ripemd160", h).digest()
    return rip.hex()

# CURVE helper (pyzmq)
def generate_curve_keypair(save_prefix: str):
    """
    Generates a libzmq CURVE keypair. Writes files:
      <save_prefix>_pub.key  (ASCII public key)
      <save_prefix>_priv.key (ASCII secret key)
    """
    pub, priv = zmq.curve_keypair()
    with open(f"{save_prefix}_pub.key", "wb") as f:
        f.write(pub)
    with open(f"{save_prefix}_priv.key", "wb") as f:
        f.write(priv)
    print(f"Generated keys: {save_prefix}_pub.key , {save_prefix}_priv.key")
    return pub, priv

def load_keyfile(path: str) -> bytes:
    with open(path, "rb") as f:
        return f.read().strip()

# -------------------------
# TX / UTXO structures
# -------------------------
@dataclass
class TXOutput:
    value: int
    address: str

@dataclass
class TXInput:
    prev_txid: str
    prev_index: int
    signature: Optional[str] = None  # "<sig_hex>:<pubkey_hex>"

@dataclass
class Transaction:
    txid: str
    inputs: List[TXInput]
    outputs: List[TXOutput]

    def to_json(self):
        return json.dumps({"txid": self.txid,
                           "inputs":[asdict(i) for i in self.inputs],
                           "outputs":[asdict(o) for o in self.outputs]}, sort_keys=True)

    @staticmethod
    def from_json(s: str):
        j = json.loads(s)
        ins = [TXInput(**i) for i in j["inputs"]]
        outs = [TXOutput(**o) for o in j["outputs"]]
        return Transaction(txid=j["txid"], inputs=ins, outputs=outs)

def input_sighash(inputs: List[TXInput], outputs: List[TXOutput], signing_index: int) -> bytes:
    # canonicalized minimal sighash: inputs (prev outpoints only), outputs, signing_index
    in_repr = [{"prev_txid": i.prev_txid, "prev_index": i.prev_index} for i in inputs]
    out_repr = [asdict(o) for o in outputs]
    payload = {"inputs": in_repr, "outputs": out_repr, "index": signing_index}
    return sha256(json.dumps(payload, sort_keys=True).encode())

def compute_txid(inputs: List[TXInput], outputs: List[TXOutput]) -> str:
    s = json.dumps({"inputs": [asdict(i) for i in inputs], "outputs":[asdict(o) for o in outputs]}, sort_keys=True).encode()
    return sha256(s).hex()

# -------------------------
# Chain storage w/ headers & reorg support
# -------------------------
class NodeChain:
    """
    sqlite-backed chain.
    Tables:
      headers: header_hash, prev_hash, height, timestamp, nonce
      blocks: block_hash, header_hash, txs_json
      utxos: txid, idx, value, address, spent
      mempool: txid, tx_json
    Reorg handling:
      - store headers and blocks
      - when a new block arrives with header that connects to a non-tip branch, we still store it
      - when a longer chain is found (tip height larger than current), we rebuild UTXO by replaying blocks from genesis following highest-work chain (we use simple height as proxy for work)
    """
    def __init__(self, network: str, port: int):
        self.network = network
        self.port = port
        self.db = DB_TEMPLATE.format(network=network, port=port)
        self.conn = sqlite3.connect(self.db, check_same_thread=False)
        self._init_db()
        if self.get_tip_height() is None:
            self._create_genesis()
        self.lock = threading.Lock()

    def _init_db(self):
        c = self.conn.cursor()
        c.execute("""CREATE TABLE IF NOT EXISTS headers (header_hash TEXT PRIMARY KEY, prev_hash TEXT, height INTEGER, timestamp INTEGER, nonce INTEGER)""")
        c.execute("""CREATE TABLE IF NOT EXISTS blocks (block_hash TEXT PRIMARY KEY, header_hash TEXT, txs TEXT)""")
        c.execute("""CREATE TABLE IF NOT EXISTS utxos (txid TEXT, idx INTEGER, value INTEGER, address TEXT, spent INTEGER DEFAULT 0, PRIMARY KEY(txid, idx))""")
        c.execute("""CREATE TABLE IF NOT EXISTS mempool (txid TEXT PRIMARY KEY, tx TEXT)""")
        self.conn.commit()

    def _create_genesis(self):
        # create genesis header at height 0
        genesis_header = ("0"*64, "", 0, int(time.time()), 0)
        c = self.conn.cursor()
        c.execute("INSERT OR IGNORE INTO headers (header_hash, prev_hash, height, timestamp, nonce) VALUES (?,?,?,?,?)", genesis_header)
        # genesis block with no txs
        c.execute("INSERT OR IGNORE INTO blocks (block_hash, header_hash, txs) VALUES (?,?,?)", ("0"*64, "0"*64, json.dumps([])))
        self.conn.commit()
        # ensure utxos empty

    def insert_block(self, prev_hash: str, nonce: int, txs: List[Transaction], timestamp: Optional[int]=None) -> Tuple[int,str]:
        """
        Store block header + block and attempt to attach. Returns new tip height and tip header hash.
        On reorg detection, may rebuild UTXO set.
        """
        if timestamp is None:
            timestamp = int(time.time())
        with self.lock:
            # compute header hash deterministically from prev_hash + timestamp + nonce + txids (header-first includes txids hashed)
            txs_json_arr = [t.to_json() for t in txs]
            header_bytes = f"{prev_hash}{timestamp}{nonce}{json.dumps(txs_json_arr, sort_keys=True)}".encode()
            header_hash = sha256(header_bytes).hex()
            block_hash = sha256((header_hash + "block").encode()).hex()  # distinct
            c = self.conn.cursor()
            # compute height for this header if prev present
            c.execute("SELECT height FROM headers WHERE header_hash = ?", (prev_hash,))
            row = c.fetchone()
            if row:
                prev_height = row[0]
                height = prev_height + 1
            else:
                # parent unknown, mark height as NULL for now (-1)
                height = -1
            c.execute("INSERT OR REPLACE INTO headers (header_hash, prev_hash, height, timestamp, nonce) VALUES (?,?,?,?,?)",
                      (header_hash, prev_hash, height if height>=0 else None, timestamp, nonce))
            c.execute("INSERT OR REPLACE INTO blocks (block_hash, header_hash, txs) VALUES (?,?,?)", (block_hash, header_hash, json.dumps(txs_json_arr)))
            self.conn.commit()

            # if parent known and parent was tip, attach normally, else we may have created a fork or orphan
            tip_height = self.get_current_tip_height()
            # find best header (max height) — if header heights are None for orphans, attempt to assign heights by walking from existing known heights
            self._recompute_header_heights()
            best_tip_height, best_tip_hash = self._find_best_tip()
            # If best_tip_height > previous tip_height, we adopt and rebuild UTXO (safe approach)
            if best_tip_height is None:
                # weird; nothing to do
                return -1, ""
            current_height = tip_height if tip_height is not None else 0
            if best_tip_height > current_height:
                # rebuild utxos by replaying blocks from genesis to best_tip_hash
                self._rebuild_utxos_from_chain(best_tip_hash)
            # return latest tip info
            final_tip_h, final_tip_hash = self._find_best_tip()
            return final_tip_h, final_tip_hash

    def _recompute_header_heights(self):
        """
        Walk headers, compute heights for reachable headers from genesis. Simple iterative approach.
        """
        c = self.conn.cursor()
        # set all heights to NULL first except genesis
        c.execute("UPDATE headers SET height = NULL WHERE header_hash != ?", ("0"*64,))
        # loop until no changes: any header whose prev has height set can set its own height
        changed = True
        while changed:
            changed = False
            c.execute("SELECT header_hash, prev_hash, height FROM headers WHERE height IS NULL")
            rows = c.fetchall()
            for header_hash, prev_hash, _ in rows:
                c2 = self.conn.cursor()
                c2.execute("SELECT height FROM headers WHERE header_hash = ?", (prev_hash,))
                r = c2.fetchone()
                if r and r[0] is not None:
                    newh = r[0] + 1
                    c2.execute("UPDATE headers SET height = ? WHERE header_hash = ?", (newh, header_hash))
                    changed = True
            if changed:
                self.conn.commit()

    def _find_best_tip(self) -> Tuple[Optional[int], Optional[str]]:
        c = self.conn.cursor()
        c.execute("SELECT header_hash, height FROM headers WHERE height IS NOT NULL ORDER BY height DESC LIMIT 1")
        r = c.fetchone()
        if not r:
            return None, None
        return r[1], r[0]  # height, header_hash (note reversed intentionally for readability)

    def get_tip_height(self) -> Optional[int]:
        c = self.conn.cursor()
        c.execute("SELECT height FROM headers WHERE header_hash = (SELECT header_hash FROM headers WHERE height = (SELECT MAX(height) FROM headers))")
        row = c.fetchone()
        return row[0] if row else 0

    def get_current_tip_height(self) -> Optional[int]:
        c = self.conn.cursor()
        c.execute("SELECT MAX(height) FROM headers WHERE height IS NOT NULL")
        r = c.fetchone()
        return r[0] if r and r[0] is not None else 0

    def get_chain_block_hashes_from_tip(self, tip_header_hash: str) -> List[str]:
        """
        Walk back from tip header to genesis collecting header_hashes, then map to block_hash via blocks table
        Returns list from genesis..tip of block_hashes to replay.
        """
        c = self.conn.cursor()
        # build header chain
        header_chain = []
        cur = tip_header_hash
        while cur and cur != "":
            header_chain.append(cur)
            c.execute("SELECT prev_hash FROM headers WHERE header_hash = ?", (cur,))
            r = c.fetchone()
            if not r:
                break
            cur = r[0]
            if cur == "":  # genesis prev is empty
                break
        header_chain = list(reversed(header_chain))
        block_hashes = []
        for h in header_chain:
            c.execute("SELECT block_hash, txs FROM blocks WHERE header_hash = ?", (h,))
            r = c.fetchone()
            if r:
                block_hashes.append((r[0], r[1]))
        return block_hashes

    def _rebuild_utxos_from_chain(self, tip_header_hash: str):
        """
        Clears utxos and replay all blocks from genesis to tip to reconstruct UTXO set.
        (Inefficient but simple and correct for small testnets.)
        """
        c = self.conn.cursor()
        print("[chain] Rebuilding UTXO set from chain...")
        c.execute("DELETE FROM utxos")
        self.conn.commit()
        # get block txs from genesis..tip
        blks = self.get_chain_block_hashes_from_tip(tip_header_hash)
        for block_hash, txs_json in blks:
            txs_list = json.loads(txs_json or "[]")
            for t_json in txs_list:
                tx = Transaction.from_json(t_json)
                # mark inputs spent (if exist)
                for vin in tx.inputs:
                    # skip coinbase sentinel inputs
                    if vin.prev_txid.startswith("coinbase_"):
                        continue
                    c.execute("UPDATE utxos SET spent = 1 WHERE txid = ? AND idx = ?", (vin.prev_txid, vin.prev_index))
                # add outputs
                for idx, out in enumerate(tx.outputs):
                    c.execute("INSERT OR REPLACE INTO utxos (txid, idx, value, address, spent) VALUES (?,?,?,?,0)",
                              (tx.txid, idx, out.value, out.address))
        self.conn.commit()
        print("[chain] UTXO rebuild complete.")

    # mempool & utxo helpers
    def add_tx_to_mempool(self, tx: Transaction) -> bool:
        with self.lock:
            if not self.verify_tx(tx):
                return False
            c = self.conn.cursor()
            c.execute("INSERT OR REPLACE INTO mempool (txid, tx) VALUES (?,?)", (tx.txid, tx.to_json()))
            self.conn.commit()
            return True

    def get_mempool_txs(self) -> List[Transaction]:
        c = self.conn.cursor()
        c.execute("SELECT tx FROM mempool")
        rows = c.fetchall()
        return [Transaction.from_json(r[0]) for r in rows]

    def clear_mempool(self):
        c = self.conn.cursor()
        c.execute("DELETE FROM mempool")
        self.conn.commit()

    def verify_tx(self, tx: Transaction, allow_coinbase: bool=False) -> bool:
        if len(tx.inputs) == 0:
            return allow_coinbase
        c = self.conn.cursor()
        total_in = 0
        for i, vin in enumerate(tx.inputs):
            c.execute("SELECT txid, idx, value, address, spent FROM utxos WHERE txid = ? AND idx = ?", (vin.prev_txid, vin.prev_index))
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

    def total_minted(self) -> int:
        c = self.conn.cursor()
        c.execute("SELECT txs FROM blocks")
        rows = c.fetchall()
        tot = 0
        for (txs,) in rows:
            for t_json in json.loads(txs or "[]"):
                t = Transaction.from_json(t_json)
                for o in t.outputs:
                    tot += o.value
        return tot

    def utxos_for_address(self, address: str) -> List[Tuple[str,int,int]]:
        c = self.conn.cursor()
        c.execute("SELECT txid, idx, value FROM utxos WHERE address = ? AND spent = 0", (address,))
        return c.fetchall()

# -------------------------
# Secure ZMQ Node (CURVE + PUB/SUB + REP)
# -------------------------
class ZMQSecureNode:
    def __init__(self, network: str,
                 pub_bind: str, rpc_bind: str,
                 server_pubkey_file: str, server_privkey_file: str,
                 peer_pub_endpoints: List[str],
                 port: int,
                 allowed_client_pubkeys: List[str]=None,
                 target=DEFAULT_TARGET):
        """
        server_pubkey_file / server_privkey_file: node's CURVE keypair (public and secret files)
        peer_pub_endpoints: list of other nodes' PUB endpoints to SUB to (tcp://host:port)
        allowed_client_pubkeys: list of client public keys bytes (optional) — not strictly enforced here, but can be checked
        """
        self.network = network
        self.pub_bind = pub_bind
        self.rpc_bind = rpc_bind
        self.peer_pubs = peer_pub_endpoints
        self.port = port
        self.target = target

        # load server keys
        self.server_pub = load_keyfile(server_pubkey_file)
        self.server_priv = load_keyfile(server_privkey_file)

        self.ctx = zmq.Context.instance()
        # PUB socket (server) - will bind
        self.pub = self.ctx.socket(zmq.PUB)
        # Set server CURVE keys on publisher socket before bind
        self.pub.curve_secretkey = self.server_priv
        self.pub.curve_publickey = self.server_pub
        # bind
        self.pub.bind(self.pub_bind)

        # SUB socket (client) - will connect to peer PUB endpoints
        self.sub = self.ctx.socket(zmq.SUB)
        # subscribe to our network prefix
        self.topic_prefix = (self.network + "|").encode()
        self.sub.setsockopt(zmq.SUBSCRIBE, self.topic_prefix)
        # SUB socket must have a client keypair to perform CURVE auth when connecting to servers:
        # It will use 'client_priv' and 'client_pub' set later by wallet/peer code before connecting.
        # For node-to-node connections we still need a client keypair; we expect the environment to have one.
        # We'll set the socket curve keys if environment variables provided.
        # Connect to peers (assumes peer PUBs are also CURVE-enabled servers)
        # Note: clients must set CURVE_SERVERKEY to peer's pubkey before connecting.
        for endpoint in self.peer_pubs:
            # For demo, we simply connect; the calling process should set required socket options beforehand if needed
            self.sub.connect(endpoint)

        # REP socket for RPC (server)
        self.rep = self.ctx.socket(zmq.REP)
        self.rep.curve_secretkey = self.server_priv
        self.rep.curve_publickey = self.server_pub
        self.rep.bind(self.rpc_bind)

        # chain
        self.chain = NodeChain(network=self.network, port=self.port)

        # runtime control
        self.running = False
        self.threads = []

    def start(self):
        self.running = True
        t_sub = threading.Thread(target=self._sub_loop, daemon=True); t_sub.start(); self.threads.append(t_sub)
        t_rep = threading.Thread(target=self._rep_loop, daemon=True); t_rep.start(); self.threads.append(t_rep)
        print(f"[node] started. PUB bind {self.pub_bind}   RPC bind {self.rpc_bind}   SUB peers {self.peer_pubs}")

    def stop(self):
        self.running = False
        time.sleep(0.2)
        try:
            self.pub.close(); self.sub.close(); self.rep.close(); self.ctx.term()
        except:
            pass

    def _sub_loop(self):
        poll = zmq.Poller()
        poll.register(self.sub, zmq.POLLIN)
        while self.running:
            socks = dict(poll.poll(300))
            if self.sub in socks and socks[self.sub] == zmq.POLLIN:
                raw = self.sub.recv()  # topic|payload
                try:
                    payload_bytes = raw[len(self.topic_prefix):]
                    obj = json.loads(payload_bytes.decode())
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
                print("[gossip] tx handling error", e)
        elif typ == "block":
            try:
                block = payload
                txs = [Transaction.from_json(tj) for tj in block.get("txs", [])]
                prev_hash = block.get("prev_hash")
                nonce = block.get("nonce")
                ts = block.get("timestamp")
                tip_h, tip_hash = self.chain.insert_block(prev_hash=prev_hash, nonce=nonce, txs=txs, timestamp=ts)
                print(f"[gossip] inserted block; new tip height {tip_h}")
                # clear mempool if some txs now included
                self.chain.clear_mempool()
            except Exception as e:
                print("[gossip] block handling error", e)
        else:
            pass

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
                        # broadcast to peers
                        self._publish({"type":"tx","payload":tx.to_json()})
                    self.rep.send_json({"type":"ack", "payload":{"accepted": ok, "txid": tx.txid}})
                except Exception as e:
                    self.rep.send_json({"type":"error", "payload": {"msg": str(e)}})
            elif typ == "get_utxos":
                addr = payload.get("address")
                utx = [{"txid":txid, "idx":idx, "value":value} for (txid, idx, value) in self.chain.utxos_for_address(addr)]
                self.rep.send_json({"type":"utxos", "payload": utx})
            elif typ == "get_tip":
                h, tip = self._get_best_tip_info()
                self.rep.send_json({"type":"tip", "payload":{"height":h,"tip":tip}})
            elif typ == "publish_block":
                # wallet/miner can call this RPC to ask node to insert block and broadcast
                try:
                    block = payload
                    txs = [Transaction.from_json(tj) for tj in block.get("txs",[])]
                    prev_hash = block.get("prev_hash")
                    nonce = block.get("nonce")
                    ts = block.get("timestamp")
                    h, tiphash = self.chain.insert_block(prev_hash=prev_hash, nonce=nonce, txs=txs, timestamp=ts)
                    self.chain.clear_mempool()
                    self._publish({"type":"block", "payload": block})
                    self.rep.send_json({"type":"ack", "payload":{"accepted": True, "height": h}})
                except Exception as e:
                    self.rep.send_json({"type":"ack", "payload":{"accepted": False, "error": str(e)}})
            else:
                self.rep.send_json({"type":"error", "payload":{"msg":"unknown"}})

    def _publish(self, obj: dict):
        payload = self.network + "|" + json.dumps(obj)
        try:
            self.pub.send_string(payload)
        except Exception as e:
            print("[publish] error", e)

    def _get_best_tip_info(self):
        h = self.chain.get_current_tip_height()
        # get header hash
        c = self.chain.conn.cursor()
        c.execute("SELECT header_hash FROM headers WHERE height = (SELECT MAX(height) FROM headers WHERE height IS NOT NULL)")
        r = c.fetchone()
        return (h, r[0] if r else "")

# -------------------------
# Miner (local)
# -------------------------
class Miner(threading.Thread):
    def __init__(self, node: ZMQSecureNode, coinbase_address: str, target=DEFAULT_TARGET):
        super().__init__(daemon=True)
        self.node = node
        self.chain = node.chain
        self.address = coinbase_address
        self.target = target
        self._stop = threading.Event()

    def stop(self):
        self._stop.set()

    def run(self):
        while not self._stop.is_set():
            tip_height = self.chain.get_current_tip_height()
            # find tip header hash
            c = self.chain.conn.cursor()
            c.execute("SELECT header_hash FROM headers WHERE height = (SELECT MAX(height) FROM headers WHERE height IS NOT NULL)")
            r = c.fetchone()
            tip_header = r[0] if r else "0"*64
            next_height = tip_height + 1 if tip_height is not None else 1
            reward = REWARD_PER_BLOCK_UNITS
            if next_height == BLOCKS_IN_EMISSION:
                reward += REWARD_REMAINDER_UNITS
            coinbase_tx = Transaction(txid=f"coinbase_{int(time.time())}_{os.getpid()}", inputs=[], outputs=[TXOutput(value=reward, address=self.address)])
            # include verified mempool txs
            candidates = [coinbase_tx] + [tx for tx in self.chain.get_mempool_txs() if self.chain.verify_tx(tx)]
            ts = int(time.time())
            nonce = 0
            found = False
            while not self._stop.is_set() and not found:
                header_b = f"{tip_header}{ts}{nonce}{json.dumps([t.to_json() for t in candidates], sort_keys=True)}".encode()
                hv = int.from_bytes(sha256(header_b), 'big')
                if hv < self.target:
                    # insert block via chain insert and publish
                    try:
                        tip_h, tip_hash = self.chain.insert_block(prev_hash=tip_header, nonce=nonce, txs=candidates, timestamp=ts)
                    except Exception as e:
                        print("[miner] block insert failed:", e)
                        break
                    self.chain.clear_mempool()
                    block_obj = {"prev_hash": tip_header, "nonce": nonce, "timestamp": ts, "txs": [t.to_json() for t in candidates]}
                    # publish via node (which will broadcast)
                    self.node._publish({"type":"block", "payload": block_obj})
                    print(f"[miner] mined block height {tip_h}")
                    found = True
                    break
                nonce += 1
                if nonce % 2000 == 0:
                    time.sleep(0)
            # loop

# -------------------------
# Simple Wallet CLI (uses CURVE to talk to node RPC)
# -------------------------
class WalletCLI:
    def __init__(self, rpc_connect: str, client_pub_file: str, client_priv_file: str, server_pub_file: str):
        self.rpc_connect = rpc_connect
        # prepare a zmq REQ socket with CURVE client keys and server public key
        self.ctx = zmq.Context.instance()
        self.sock = self.ctx.socket(zmq.REQ)
        # load client keys
        client_pub = load_keyfile(client_pub_file)
        client_priv = load_keyfile(client_priv_file)
        server_pub = load_keyfile(server_pub_file)
        self.sock.curve_publickey = client_pub
        self.sock.curve_secretkey = client_priv
        # must tell socket server pubkey to authenticate the server
        self.sock.curve_serverkey = server_pub
        self.sock.connect(self.rpc_connect)
        self.sk = None  # ECDSA signing key (wallet)
        self.pub = None
        self.address = None

    def generate_wallet_key(self):
        sk = SigningKey.generate(curve=SECP256k1)
        self.sk = sk
        self.pub = sk.get_verifying_key().to_string()
        self.address = pubkey_to_address(self.pub)
        print("[wallet] generated address", self.address)

    def load_wallet_key_hex(self, hexstr: str):
        sk = SigningKey.from_string(bytes.fromhex(hexstr), curve=SECP256k1)
        self.sk = sk
        self.pub = sk.get_verifying_key().to_string()
        self.address = pubkey_to_address(self.pub)

    def rpc_call(self, obj: dict, timeout=4.0) -> dict:
        try:
            self.sock.send_json(obj)
            resp = self.sock.recv_json()
            return resp
        except Exception as e:
            return {"type":"error","payload":{"msg":str(e)}}

    def get_utxos(self):
        if not self.address:
            print("No wallet loaded")
            return []
        res = self.rpc_call({"type":"get_utxos","payload":{"address": self.address}})
        if res.get("type") == "utxos":
            return res.get("payload", [])
        print("RPC error", res)
        return []

    def send_tx(self, to_address: str, amount_coins: float):
        if not self.sk or not self.address:
            print("Load/generate a wallet key first")
            return
        amt_units = int(math.floor(amount_coins * COIN))
        utxos = self.get_utxos()
        if not utxos:
            print("No funds")
            return
        selected = []
        total = 0
        for u in utxos:
            selected.append((u["txid"], u["idx"], u["value"]))
            total += u["value"]
            if total >= amt_units:
                break
        if total < amt_units:
            print("Insufficient funds")
            return
        inputs = [TXInput(prev_txid=txid, prev_index=idx, signature=None) for (txid, idx, _v) in selected]
        outputs = [TXOutput(value=amt_units, address=to_address)]
        change = total - amt_units
        if change > 0:
            outputs.append(TXOutput(value=change, address=self.address))
        # sign per-input
        for i in range(len(inputs)):
            digest = input_sighash(inputs, outputs, i)
            sig = self.sk.sign_deterministic(digest)
            inputs[i].signature = f"{sig.hex()}:{self.sk.get_verifying_key().to_string().hex()}"
        txid = compute_txid(inputs, outputs)
        tx = Transaction(txid=txid, inputs=inputs, outputs=outputs)
        resp = self.rpc_call({"type":"submit_tx", "payload": tx.to_json()})
        print("submit_tx response:", resp)

# -------------------------
# CLI / runner
# -------------------------
def main():
    p = argparse.ArgumentParser()
    p.add_argument("--node", action="store_true")
    p.add_argument("--wallet", action="store_true")
    p.add_argument("--network", default="testnet", choices=["testnet","mainnet"])
    p.add_argument("--pub-bind", default="tcp://*:30001")
    p.add_argument("--rpc-bind", default="tcp://*:30002")
    p.add_argument("--peer-pubs", default="", help="Comma-separated peer PUB endpoints to SUB to (e.g. tcp://host:31001)")
    p.add_argument("--port", type=int, default=30001, help="node numeric id for DB filename")
    p.add_argument("--pub-key-file", default="node_pub.key", help="node CURVE public key file")
    p.add_argument("--priv-key-file", default="node_priv.key", help="node CURVE private key file")
    p.add_argument("--client-pub", default="client_pub.key")
    p.add_argument("--client-priv", default="client_priv.key")
    p.add_argument("--rpc-connect", default="tcp://localhost:30002")
    p.add_argument("--generate-curve-keys", default="", help="If provided, generate a curve keypair prefix")
    args = p.parse_args()

    if args.generate_curve_keys:
        generate_curve_keypair(args.generate_curve_keys)
        return

    if args.node:
        peers = [x.strip() for x in args.peer_pubs.split(",") if x.strip()]
        node = ZMQSecureNode(network=args.network,
                             pub_bind=args.pub_bind, rpc_bind=args.rpc_bind,
                             server_pubkey_file=args.pub_key_file, server_privkey_file=args.priv_key_file,
                             peer_pub_endpoints=peers, port=args.port)
        node.start()
        miner = None
        try:
            while True:
                cmd = input("node> ").strip().split()
                if not cmd: continue
                if cmd[0] == "exit": break
                if cmd[0] == "status":
                    print("tip height:", node.chain.get_current_tip_height(), "minted:", node.chain.total_minted()/COIN)
                elif cmd[0] == "mine-start" and len(cmd) >= 2:
                    if miner:
                        print("miner running")
                    else:
                        miner = Miner(node, cmd[1]); miner.start(); print("miner started")
                elif cmd[0] == "mine-stop":
                    if miner:
                        miner.stop(); miner = None; print("miner stopped")
                    else:
                        print("no miner")
                elif cmd[0] == "utxos" and len(cmd)>=2:
                    print(node.chain.utxos_for_address(cmd[1]))
                elif cmd[0] == "mempool":
                    print([tx.txid for tx in node.chain.get_mempool_txs()])
                else:
                    print("unknown command")
        except KeyboardInterrupt:
            pass
        finally:
            if miner: miner.stop()
            node.stop()

    elif args.wallet:
        wallet = WalletCLI(rpc_connect=args.rpc_connect, client_pub_file=args.client_pub, client_priv_file=args.client_priv, server_pub_file=args.pub_key_file)
        print("Wallet CLI. Commands: gen, loadhex <hexsk>, utxos, send <to> <amount>, exit")
        try:
            while True:
                cmd = input("wallet> ").strip().split()
                if not cmd: continue
                if cmd[0] == "exit": break
                if cmd[0] == "gen":
                    wallet.generate_wallet_key()
                elif cmd[0] == "loadhex" and len(cmd) >= 2:
                    wallet.load_wallet_key_hex(cmd[1])
                elif cmd[0] == "utxos":
                    print(wallet.get_utxos())
                elif cmd[0] == "send" and len(cmd) >= 3:
                    to = cmd[1]; amt = float(cmd[2]); wallet.send_tx(to, amt)
                else:
                    print("unknown")
        except KeyboardInterrupt:
            pass
    else:
        print("Pick --node or --wallet. Use --generate-curve-keys <prefix> to create CURVE keys first.")

if __name__ == "__main__":
    main()
