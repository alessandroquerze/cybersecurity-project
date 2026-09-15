#!/usr/bin/env python3
"""
PC side of the ESP8266 PSK-authenticated ECDH secure channel.

Dependencies:
    pip install cryptography

Commands while connected:
    +       increase X by 1 second
    -       decrease X by 1 second
    +5      increase X by 5 seconds
    -5      decrease X by 5 seconds
    set 10  set X to 10 seconds
    get     ask the ESP for the current X
    quit    close the PC program
"""

from __future__ import annotations

import hmac
import hashlib
import socket
import struct
import threading
import sys
from dataclasses import dataclass

from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF


HOST = "0.0.0.0"
PORT = 1988

# Must be identical to the ESP8266 PSK.
PSK = bytes([
    0x2A,0xF1,0x44,0x90,0x31,0xC2,0x77,0x5B,
    0x9D,0xA8,0x13,0x6E,0x54,0xB7,0xC0,0x22,
    0x7A,0x61,0xE3,0x18,0x8B,0xD4,0x45,0xF9,
    0x03,0xCC,0x6D,0x71,0xAF,0x5E,0x92,0x10
])

VERSION = 1

HS_SERVER_HELLO = 0x10
HS_CLIENT_HELLO = 0x11
HS_SERVER_FINISH = 0x12
FRAME_SECURE = 0x20

NONCE_LEN = 32
PUB_LEN = 64
HMAC_LEN = 32
GCM_TAG_LEN = 16
MAX_CIPHERTEXT = 144

INFO = b"esp8266-psk-ecdh-v1"


def recv_exact(sock: socket.socket, n: int) -> bytes:
    out = bytearray()
    while len(out) < n:
        chunk = sock.recv(n - len(out))
        if not chunk:
            raise ConnectionError("peer disconnected")
        out.extend(chunk)
    return bytes(out)


def raw_public_key(pub: ec.EllipticCurvePublicKey) -> bytes:
    encoded = pub.public_bytes(
        serialization.Encoding.X962,
        serialization.PublicFormat.UncompressedPoint,
    )
    if len(encoded) != 65 or encoded[0] != 0x04:
        raise ValueError("unexpected P-256 encoding")
    return encoded[1:]  # micro-ecc uses X||Y, 64 bytes


def public_from_raw(raw: bytes) -> ec.EllipticCurvePublicKey:
    if len(raw) != 64:
        raise ValueError("P-256 public key must be 64 bytes")
    encoded = b"\x04" + raw
    return ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), encoded)


def transcript(role: bytes, ns: bytes, ps: bytes, nc: bytes, pc: bytes) -> bytes:
    return role + bytes([VERSION]) + ns + ps + nc + pc


@dataclass
class SecureChannel:
    sock: socket.socket
    send_key: bytes
    recv_key: bytes
    send_seed: bytes
    recv_seed: bytes
    send_counter: int = 0
    recv_counter: int = 0

    @staticmethod
    def _iv(seed: bytes, counter: int) -> bytes:
        if len(seed) != 8:
            raise ValueError("bad IV seed")
        return seed + struct.pack(">I", counter)

    def send_text(self, text: str) -> None:
        data = text.encode("utf-8")
        if len(data) > 128:
            raise ValueError("message too long")
        if self.send_counter >= 0xFFFFFFFF:
            raise RuntimeError("counter exhausted: reconnect required")

        self.send_counter += 1
        counter = self.send_counter
        aad = struct.pack(">I", counter)
        iv = self._iv(self.send_seed, counter)

        # cryptography AESGCM appends the 16-byte tag to ciphertext.
        ciphertext = AESGCM(self.send_key).encrypt(iv, data, aad)
        header = struct.pack(">BIH", FRAME_SECURE, counter, len(ciphertext))
        self.sock.sendall(header + ciphertext)

    def receive_text(self) -> str:
        header = recv_exact(self.sock, 7)
        frame_type, counter, clen = struct.unpack(">BIH", header)

        if frame_type != FRAME_SECURE:
            raise ValueError(f"unexpected frame type 0x{frame_type:02x}")
        if counter <= self.recv_counter:
            raise ValueError("replay/out-of-order packet rejected")
        if clen < GCM_TAG_LEN or clen > MAX_CIPHERTEXT:
            raise ValueError("invalid ciphertext length")

        ciphertext = recv_exact(self.sock, clen)
        aad = struct.pack(">I", counter)
        iv = self._iv(self.recv_seed, counter)

        # Tag verification happens inside decrypt().
        plaintext = AESGCM(self.recv_key).decrypt(iv, ciphertext, aad)

        # Only advance after successful authentication.
        self.recv_counter = counter
        return plaintext.decode("utf-8")


def server_handshake(sock: socket.socket) -> SecureChannel:
    # Ephemeral server ECDH key.
    server_priv = ec.generate_private_key(ec.SECP256R1())
    ps = raw_public_key(server_priv.public_key())
    ns = __import__("os").urandom(NONCE_LEN)

    # 1) SERVER_HELLO
    sock.sendall(bytes([HS_SERVER_HELLO, VERSION]) + ns + ps)

    # 2) CLIENT_HELLO
    prefix = recv_exact(sock, 2)
    if prefix != bytes([HS_CLIENT_HELLO, VERSION]):
        raise ValueError("bad client hello")

    nc = recv_exact(sock, NONCE_LEN)
    pc = recv_exact(sock, PUB_LEN)
    mac_c = recv_exact(sock, HMAC_LEN)

    expected_c = hmac.new(
        PSK,
        transcript(b"C", ns, ps, nc, pc),
        hashlib.sha256,
    ).digest()

    if not hmac.compare_digest(mac_c, expected_c):
        raise PermissionError("client PSK authentication failed")

    # Validate/parse client point before ECDH.
    client_pub = public_from_raw(pc)

    # 3) SERVER_FINISH authenticates server to ESP and binds same transcript.
    mac_s = hmac.new(
        PSK,
        transcript(b"S", ns, ps, nc, pc),
        hashlib.sha256,
    ).digest()
    sock.sendall(bytes([HS_SERVER_FINISH]) + mac_s)

    # ECDH shared secret.
    shared = server_priv.exchange(ec.ECDH(), client_pub)

    # Independent traffic keys, bound to both fresh nonces.
    material = HKDF(
        algorithm=hashes.SHA256(),
        length=80,
        salt=ns + nc,
        info=INFO,
    ).derive(shared)

    # Server -> ESP
    send_key = material[0:32]
    send_seed = material[32:40]

    # ESP -> Server
    recv_key = material[40:72]
    recv_seed = material[72:80]

    return SecureChannel(sock, send_key, recv_key, send_seed, recv_seed)


def receiver_loop(channel: SecureChannel, stop: threading.Event) -> None:
    try:
        while not stop.is_set():
            msg = channel.receive_text()
            if msg.startswith("TIME|"):
                print(f"\n[ESP time] {msg[5:]}")
            elif msg.startswith("INTERVAL|"):
                print(f"\n[ESP] X = {msg[9:]} s")
            else:
                print(f"\n[ESP] {msg}")
            print("> ", end="", flush=True)
    except Exception as exc:
        if not stop.is_set():
            print(f"\n[receiver stopped] {exc}")
        stop.set()


def command_to_protocol(line: str) -> str | None:
    s = line.strip().lower()

    if s in {"quit", "exit"}:
        return None
    if s == "+":
        return "INC|1"
    if s == "-":
        return "DEC|1"
    if s.startswith("+") and s[1:].isdigit():
        return f"INC|{int(s[1:])}"
    if s.startswith("-") and s[1:].isdigit():
        return f"DEC|{int(s[1:])}"
    if s.startswith("set "):
        value = s.split(maxsplit=1)[1]
        if value.isdigit():
            return f"SET|{int(value)}"
    if s == "get":
        return "GET"

    print("Commands: +  -  +N  -N  set N  get  quit")
    return ""


def serve_once() -> None:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as server:
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.bind((HOST, PORT))
        server.listen(1)

        print(f"Listening on {HOST}:{PORT}")
        print("Waiting for ESP8266 ...")

        conn, addr = server.accept()
        with conn:
            conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            print(f"TCP connected from {addr}; channel is NOT secure yet.")

            channel = server_handshake(conn)
            print("PSK-authenticated ECDH handshake complete.")
            print("AES-256-GCM secure channel ready.")
            print("Commands: +  -  +N  -N  set N  get  quit")

            stop = threading.Event()
            rx = threading.Thread(
                target=receiver_loop,
                args=(channel, stop),
                daemon=True,
            )
            rx.start()

            try:
                while not stop.is_set():
                    line = input("> ")
                    cmd = command_to_protocol(line)
                    if cmd is None:
                        stop.set()
                        break
                    if cmd:
                        channel.send_text(cmd)
            except (EOFError, KeyboardInterrupt):
                stop.set()


if __name__ == "__main__":
    try:
        serve_once()
    except Exception as exc:
        print(f"Fatal: {exc}", file=sys.stderr)
        sys.exit(1)
