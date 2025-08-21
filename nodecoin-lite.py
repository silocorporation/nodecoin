#!/usr/bin/env python3
import os, hashlib, json, time, threading, zmq, ssl, socket
import ecdsa
import gi
gi.require_version("Gtk", "3.0")
from gi.repository import Gtk

# ---------------- NETWORK CONFIG ----------------
NETWORKS = {
    "mainnet": {"name": "Mainnet", "port": 8333, "genesis_block": "00"*32, "difficulty": 4},
    "testnet": {"name": "Testnet", "port": 18333, "genesis_block": "11"*32, "difficulty": 2}
}
CURRENT_NETWORK = NETWORKS["testnet"]

# ---------------- WALLET ----------------
def generate_wallet():
    priv_key = os.urandom(32)
    sk = ecdsa.SigningKey.from_string(priv_key, curve=ecdsa.SECP256k1)
    vk = sk.verifying_key
    pub_key = vk.to_string().hex()
    address = hashlib.sha256((pub_key + CURRENT_NETWORK['name']).encode()).hexdigest()
    return {"priv": priv_key.hex(), "pub": pub_key, "address": address, "sk": sk, "vk": vk}

wallet = generate_wallet()

# ---------------- BLOCKCHAIN ----------------
blockchain = [CURRENT_NETWORK["genesis_block"]]
utxos = {}

def hash_block(block):
    return hashlib.sha256(json.dumps(block, sort_keys=True).encode()).hexdigest()

def verify_transaction(tx):
    try:
        sig = bytes.fromhex(tx['sig'])
        sender_vk = ecdsa.VerifyingKey.from_string(bytes.fromhex(tx['pub']), curve=ecdsa.SECP256k1)
        sender_vk.verify(sig, tx['data'].encode())
        # Check UTXO
        inputs = tx['inputs']
        for i in inputs:
            if i not in utxos or utxos[i] < tx['amount']:
                return False
        return True
    except:
        return False

def add_block(block):
    global blockchain, utxos
    # Simple reorg handling
    if len(blockchain) > 1 and block['prev_hash'] != hash_block(blockchain[-1]):
        print("Potential reorg detected. Ignoring block for simplicity.")
        return
    for tx in block['transactions']:
        if verify_transaction(tx):
            for inp in tx['inputs']:
                utxos[inp] -= tx['amount']
            utxos[tx['address']] = utxos.get(tx['address'], 0) + tx['amount']
        else:
            print("Invalid transaction skipped")
    blockchain.append(block)

# ---------------- P2P ----------------
context = zmq.Context()
socket = context.socket(zmq.REP)
socket.bind(f"tcp://*:{CURRENT_NETWORK['port']}")
peers = set()

def sync_with_peer(peer_addr):
    try:
        peer = context.socket(zmq.REQ)
        peer.connect(f"tcp://{peer_addr}")
        peer.send_json({"cmd": "get_head"})
        head_block = peer.recv_json()
        if hash_block(head_block) != hash_block(blockchain[-1]):
            add_block(head_block)
        # Get peer list
        peer.send_json({"cmd": "get_peers"})
        new_peers = peer.recv_json().get("peers", [])
        peers.update(new_peers)
        peer.close()
    except:
        peers.discard(peer_addr)

def discover_peers():
    while True:
        for peer_addr in list(peers):
            sync_with_peer(peer_addr)
        time.sleep(10)

def broadcast_tx(tx):
    for peer_addr in list(peers):
        try:
            s = context.socket(zmq.REQ)
            s.connect(f"tcp://{peer_addr}")
            s.send_json({"cmd": "tx", "tx": tx})
            s.recv_json()
            s.close()
        except:
            peers.discard(peer_addr)

def listen_for_peers():
    while True:
        msg = socket.recv_json()
        cmd = msg.get("cmd")
        if cmd == "get_head":
            socket.send_json(blockchain[-1])
        elif cmd == "get_peers":
            socket.send_json({"peers": list(peers)})
        elif cmd == "tx":
            tx = msg.get("tx")
            if verify_transaction(tx):
                print("Received valid TX:", tx)
                broadcast_tx(tx)
            socket.send_json({"status": "ok"})
        else:
            socket.send_json({"status": "unknown command"})

threading.Thread(target=listen_for_peers, daemon=True).start()
threading.Thread(target=discover_peers, daemon=True).start()

# ---------------- GTK WALLET ----------------
class WalletGUI(Gtk.Window):
    def __init__(self):
        Gtk.Window.__init__(self, title="Crypto Wallet")
        self.set_default_size(400, 200)
        box = Gtk.Box(spacing=6, orientation=Gtk.Orientation.VERTICAL)
        self.add(box)
        self.balance_label = Gtk.Label(label="Balance: 0")
        self.address_label = Gtk.Label
