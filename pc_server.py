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

# PSK (Pre-Shared Key): deve essere identica a quella salvata sull'ESP8266.
# Non viene usata direttamente per cifrare i messaggi: durante l'handshake serve
# per calcolare gli HMAC e quindi autenticare reciprocamente ESP e server.
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

NONCE_LEN = 32       # Ns/Nc: nonce casuali che rendono ogni handshake/sessione differente.
PUB_LEN = 64         # chiave pubblica P-256 in formato X || Y: 32 byte X + 32 byte Y.
HMAC_LEN = 32        # HMAC-SHA256 produce 32 byte.
GCM_TAG_LEN = 16     # tag AES-GCM: autentica il messaggio e rileva eventuali modifiche.
MAX_CIPHERTEXT = 144 # 128 byte massimi di plaintext + 16 byte di tag GCM.

# Stringa di contesto passata a HKDF: separa logicamente queste chiavi da eventuali
# altre chiavi che potrebbero essere derivate dallo stesso shared secret.
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
    # cryptography rappresenta un punto P-256 non compresso come 0x04 || X || Y
    # (65 byte totali). micro-ecc sull'ESP usa invece direttamente X || Y (64 byte).
    encoded = pub.public_bytes(
        serialization.Encoding.X962,
        serialization.PublicFormat.UncompressedPoint,
    )
    if len(encoded) != 65 or encoded[0] != 0x04:
        raise ValueError("unexpected P-256 encoding")
    return encoded[1:]  # rimuove il byte 0x04 e lascia solamente X || Y


def public_from_raw(raw: bytes) -> ec.EllipticCurvePublicKey:
    if len(raw) != 64:
        raise ValueError("P-256 public key must be 64 bytes")

    # Operazione inversa di raw_public_key(): aggiunge 0x04 davanti a X || Y,
    # così cryptography può validare il punto e ricostruire la chiave pubblica P-256.
    encoded = b"\x04" + raw
    return ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), encoded)


def transcript(role: bytes, ns: bytes, ps: bytes, nc: bytes, pc: bytes) -> bytes:
    # Il transcript mette insieme ruolo, versione, nonce e chiavi pubbliche di entrambi.
    # L'HMAC viene calcolato su questi dati per impedire che vengano sostituiti durante
    # l'handshake senza che l'altra parte se ne accorga.
    return role + bytes([VERSION]) + ns + ps + nc + pc


@dataclass
class SecureChannel:
    sock: socket.socket

    # Chiavi e seed IV separati per le due direzioni: riutilizzare la stessa coppia
    # key/IV nelle due direzioni sarebbe una cattiva pratica con AES-GCM.
    send_key: bytes
    recv_key: bytes
    send_seed: bytes
    recv_seed: bytes

    # I counter partono da zero e crescono per ogni messaggio. Servono sia a costruire
    # IV diversi sia a rifiutare pacchetti già ricevuti (replay) o fuori ordine.
    send_counter: int = 0
    recv_counter: int = 0

    @staticmethod
    def _iv(seed: bytes, counter: int) -> bytes:
        if len(seed) != 8:
            raise ValueError("bad IV seed")

        # IV AES-GCM di 12 byte = seed di sessione (8 byte) || counter (4 byte).
        # Il seed resta fisso per quella direzione durante la sessione, mentre il counter
        # cambia a ogni messaggio: in questo modo non si riutilizza lo stesso IV.
        return seed + struct.pack(">I", counter)  # >I = uint32 in Big Endian

    def send_text(self, text: str) -> None:
        data = text.encode("utf-8")
        if len(data) > 128:
            raise ValueError("message too long")
        if self.send_counter >= 0xFFFFFFFF:
            raise RuntimeError("counter exhausted: reconnect required")

        self.send_counter += 1
        counter = self.send_counter  # numero progressivo del messaggio: aiuta a impedire replay attack

        # Il counter viene anche passato come AAD (Additional Authenticated Data):
        # rimane visibile nell'header, quindi non è cifrato, ma AES-GCM lo autentica.
        # Se qualcuno modifica il counter in rete, la verifica del tag fallisce.
        aad = struct.pack(">I", counter)

        # Per ogni messaggio si costruisce un nuovo IV usando seed + counter.
        iv = self._iv(self.send_seed, counter)

        # AESGCM.encrypt usa send_key per cifrare data con questo IV.
        # Il risultato della libreria è: ciphertext || tag GCM da 16 byte.
        # Il tag serve a verificare sia l'autenticità/integrità del ciphertext sia dell'AAD.
        ciphertext = AESGCM(self.send_key).encrypt(iv, data, aad)

        # Header in chiaro: tipo(1) || counter(4) || lunghezza ciphertext+tag(2).
        # Il counter è comunque protetto contro modifiche perché è stato inserito nell'AAD.
        header = struct.pack(">BIH", FRAME_SECURE, counter, len(ciphertext))
        self.sock.sendall(header + ciphertext)

    def receive_text(self) -> str:
        header = recv_exact(self.sock, 7)
        frame_type, counter, clen = struct.unpack(">BIH", header)

        if frame_type != FRAME_SECURE:
            raise ValueError(f"unexpected frame type 0x{frame_type:02x}")
        # Se il counter non è maggiore dell'ultimo accettato, il pacchetto è vecchio,
        # duplicato oppure fuori ordine: viene rifiutato prima di elaborarlo.
        if counter <= self.recv_counter:
            raise ValueError("replay/out-of-order packet rejected")
        if clen < GCM_TAG_LEN or clen > MAX_CIPHERTEXT:
            raise ValueError("invalid ciphertext length")

        ciphertext = recv_exact(self.sock, clen)

        # Ricostruisce esattamente la stessa AAD e lo stesso IV usati dal mittente.
        aad = struct.pack(">I", counter)
        iv = self._iv(self.recv_seed, counter)

        # decrypt() riceve ciphertext || tag. La libreria verifica internamente il tag GCM:
        # se key, IV, ciphertext o AAD non coincidono con quelli originali, solleva errore
        # e il plaintext non viene considerato autentico.
        plaintext = AESGCM(self.recv_key).decrypt(iv, ciphertext, aad)

        # Il counter viene aggiornato solo DOPO una verifica GCM riuscita, altrimenti un
        # pacchetto falso con counter alto potrebbe far scartare i messaggi validi successivi.
        self.recv_counter = counter
        return plaintext.decode("utf-8")


def server_handshake(sock: socket.socket) -> SecureChannel:
    # Genera una nuova coppia ECDH P-256 effimera per questa singola sessione.
    # "Effimera" significa che a una nuova connessione verrà generata una nuova chiave privata.
    server_priv = ec.generate_private_key(ec.SECP256R1())
    ps = raw_public_key(server_priv.public_key())  # Ps = chiave pubblica ECDH del server

    # Ns = nonce casuale del server. Non è segreto: serve a rendere ogni handshake unico.
    ns = __import__("os").urandom(NONCE_LEN)

    # 1) SERVER_HELLO: invia versione, nonce server e chiave pubblica ECDH del server.
    sock.sendall(bytes([HS_SERVER_HELLO, VERSION]) + ns + ps)

    # 2) CLIENT_HELLO
    prefix = recv_exact(sock, 2)
    if prefix != bytes([HS_CLIENT_HELLO, VERSION]):
        raise ValueError("bad client hello")

    nc = recv_exact(sock, NONCE_LEN)  # Nc = nonce casuale generato dall'ESP/client
    pc = recv_exact(sock, PUB_LEN)    # Pc = chiave pubblica ECDH effimera dell'ESP/client
    mac_c = recv_exact(sock, HMAC_LEN)  # HMAC inviato dall'ESP per autenticarsi

    # Ricalcola localmente il MAC che il client avrebbe dovuto produrre conoscendo la PSK.
    # Il ruolo "C" distingue questo MAC da quello del server anche se il resto del transcript
    # è identico. In questo modo nonce e chiavi pubbliche sono tutti legati all'autenticazione.
    expected_c = hmac.new(
        PSK,
        transcript(b"C", ns, ps, nc, pc),
        hashlib.sha256,
    ).digest()

    # compare_digest effettua un confronto pensato per evitare differenze di tempo evidenti
    # tra MAC che differiscono presto o tardi, riducendo il rischio di timing attack.
    if not hmac.compare_digest(mac_c, expected_c):
        raise PermissionError("client PSK authentication failed")

    # Ricostruisce e valida Pc come punto della curva P-256 prima di usarlo nell'ECDH.
    client_pub = public_from_raw(pc)

    # 3) SERVER_FINISH: ora è il server ad autenticarsi verso l'ESP.
    mac_s = hmac.new(
        PSK,
        transcript(b"S", ns, ps, nc, pc),
        hashlib.sha256,
    ).digest()
    # L'ESP conosce la stessa PSK e può ricalcolare mac_s: se coincide, autentica il server.
    sock.sendall(bytes([HS_SERVER_FINISH]) + mac_s)

    # ECDH combina la chiave PRIVATA del server con la chiave PUBBLICA del client.
    # Sul lato ESP avviene l'operazione opposta (privata client + pubblica server) e, per
    # le proprietà matematiche dell'ECDH, entrambi ottengono lo stesso shared secret.
    shared = server_priv.exchange(ec.ECDH(), client_pub)

    # Lo shared secret ECDH non viene usato direttamente come chiave AES. HKDF-SHA256
    # lo trasforma in 80 byte di materiale crittografico adatto all'uso.
    # salt = Ns || Nc lega la derivazione a questa specifica sessione/handshake.
    # info identifica il protocollo e il contesto in cui le chiavi verranno usate.
    material = HKDF(
        algorithm=hashes.SHA256(),
        length=80,
        salt=ns + nc,
        info=INFO,
    ).derive(shared)

    # I primi 40 byte sono dedicati alla direzione Server -> ESP:
    # 32 byte di chiave AES-256 + 8 byte di seed usato per costruire gli IV.
    send_key = material[0:32]
    send_seed = material[32:40]

    # I successivi 40 byte sono dedicati alla direzione ESP -> Server.
    # Sul codice ESP questi stessi blocchi sono naturalmente chiamati recvKey/recvIvSeed
    # e sendKey/sendIvSeed con verso opposto rispetto al server.
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
