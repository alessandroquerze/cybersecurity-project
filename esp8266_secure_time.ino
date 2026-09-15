/*
  ESP8266 secure time sender
  Protocol:
    - TCP socket is considered untrusted.
    - Ephemeral ECDH P-256 provides a fresh shared secret.
    - A pre-shared key (PSK) authenticates the ECDH handshake with HMAC-SHA256.
    - HKDF-SHA256 derives independent AES-256-GCM keys for each direction.
    - AES-GCM protects confidentiality + integrity.
    - A monotonically increasing counter is authenticated and used in the IV.
    - The ESP sends TIME|HH:MM:SS every X seconds.
    - The PC can send INC|n, DEC|n, SET|n, GET.

  Arduino libraries:
    1) ESP8266 board package
    2) micro-ecc by Kenneth MacKay: https://github.com/kmackay/micro-ecc
    3) Arduino Cryptography Library by Rhys Weatherley / CryptoArduino fork:
       https://github.com/gmag11/CryptoArduino

  IMPORTANT:
    - Use the same 32-byte PSK on ESP and PC.
    - Change WIFI_SSID, WIFI_PASSWORD, SERVER_IP.
    - This demo assumes no attacker can extract the PSK from ESP flash.
*/

#include <ESP8266WiFi.h>
#include <time.h>

extern "C" {
#include <user_interface.h>   // os_get_random()
}

#include <uECC.h>
#include <Crypto.h>
#include <SHA256.h>
#include <AES.h>
#include <GCM.h>

// -------------------------- CONFIG --------------------------

const char *WIFI_SSID     = "FP5";
//const char *WIFI_PASSWORD = "CHANGE_ME"; rimossa

IPAddress SERVER_IP(10, 83, 168, 17);
const uint16_t SERVER_PORT = 1988;

// Exactly 32 bytes. Replace with a random value and copy the same bytes to pc_server.py.
static const uint8_t PSK[32] = {
  0x2A,0xF1,0x44,0x90,0x31,0xC2,0x77,0x5B,
  0x9D,0xA8,0x13,0x6E,0x54,0xB7,0xC0,0x22,
  0x7A,0x61,0xE3,0x18,0x8B,0xD4,0x45,0xF9,
  0x03,0xCC,0x6D,0x71,0xAF,0x5E,0x92,0x10
};

const char *TZ_INFO = "CET-1CEST,M3.5.0,M10.5.0/3";
const char *NTP_1 = "pool.ntp.org";
const char *NTP_2 = "time.google.com";

static uint32_t intervalSeconds = 5;
static const uint32_t MIN_INTERVAL = 1;
static const uint32_t MAX_INTERVAL = 3600;

// ------------------------ PROTOCOL --------------------------

static const uint8_t VERSION = 1;

enum HandshakeType : uint8_t {
  HS_SERVER_HELLO = 0x10,
  HS_CLIENT_HELLO = 0x11,
  HS_SERVER_FINISH = 0x12
};

enum FrameType : uint8_t {
  FRAME_SECURE = 0x20
};

static const size_t NONCE_LEN = 32;
static const size_t PUB_LEN = 64;       // micro-ecc: X || Y for secp256r1
static const size_t HMAC_LEN = 32;
static const size_t AES_KEY_LEN = 32;
static const size_t IV_SEED_LEN = 8;
static const size_t GCM_TAG_LEN = 16;
static const size_t GCM_IV_LEN = 12;
static const size_t MAX_PLAINTEXT = 128;
static const size_t MAX_CIPHERTEXT = MAX_PLAINTEXT + GCM_TAG_LEN;

WiFiClient client;

uint8_t sendKey[AES_KEY_LEN];
uint8_t recvKey[AES_KEY_LEN];
uint8_t sendIvSeed[IV_SEED_LEN];
uint8_t recvIvSeed[IV_SEED_LEN];

uint32_t sendCounter = 0;
uint32_t recvCounter = 0;
bool secureChannelReady = false;

unsigned long lastSendMs = 0;

// --------------------- LOW LEVEL HELPERS --------------------

static bool fillRandom(uint8_t *dest, unsigned size) {
  return os_get_random(dest, size) == 0;
}

static int microEccRng(uint8_t *dest, unsigned size) {
  return fillRandom(dest, size) ? 1 : 0;
}

static bool readExact(WiFiClient &c, uint8_t *buf, size_t len, uint32_t timeoutMs = 8000) {
  size_t pos = 0;
  unsigned long start = millis();
  while (pos < len) {
    if (!c.connected()) return false;
    int avail = c.available();
    if (avail > 0) {
      int n = c.read(buf + pos, len - pos);
      if (n > 0) pos += (size_t)n;
    } else {
      delay(1);
      yield();
      if (millis() - start > timeoutMs) return false;
    }
  }
  return true;
}

static bool writeExact(WiFiClient &c, const uint8_t *buf, size_t len) {
  size_t pos = 0;
  while (pos < len) {
    size_t n = c.write(buf + pos, len - pos);
    if (n == 0) return false;
    pos += n;
    yield();
  }
  return true;
}

static void writeU16BE(uint8_t out[2], uint16_t v) {
  out[0] = (uint8_t)(v >> 8);
  out[1] = (uint8_t)(v);
}

static uint16_t readU16BE(const uint8_t in[2]) {
  return ((uint16_t)in[0] << 8) | in[1];
}

static void writeU32BE(uint8_t out[4], uint32_t v) {
  out[0] = (uint8_t)(v >> 24);
  out[1] = (uint8_t)(v >> 16);
  out[2] = (uint8_t)(v >> 8);
  out[3] = (uint8_t)(v);
}

static uint32_t readU32BE(const uint8_t in[4]) {
  return ((uint32_t)in[0] << 24) |
         ((uint32_t)in[1] << 16) |
         ((uint32_t)in[2] << 8)  |
         ((uint32_t)in[3]);
}

static bool constTimeEq(const uint8_t *a, const uint8_t *b, size_t n) {
  uint8_t diff = 0;
  for (size_t i = 0; i < n; ++i) diff |= (a[i] ^ b[i]);
  return diff == 0;
}
static void secureWipe(void *ptr, size_t len) {
  volatile uint8_t *p = (volatile uint8_t *)ptr;
  while (len--) {
    *p++ = 0;
  }
}

template <size_t N>
static void secureWipe(uint8_t (&buf)[N]) {
  secureWipe(buf, N);
}
// --------------------- HMAC / HKDF --------------------------

static void hmacSha256(const uint8_t *key, size_t keyLen,
                       const uint8_t *data, size_t dataLen,
                       uint8_t out[32]) {
  hmac<SHA256>(out, 32, key, keyLen, data, dataLen);
}

// HKDF RFC 5869, SHA-256. 
static bool hkdfSha256(const uint8_t *ikm, size_t ikmLen,
                       const uint8_t *salt, size_t saltLen,
                       const uint8_t *info, size_t infoLen,
                       uint8_t *out, size_t outLen) {
  if (outLen > 255 * 32) return false;

  uint8_t zeroSalt[32] = {0};
  const uint8_t *actualSalt = saltLen ? salt : zeroSalt;
  size_t actualSaltLen = saltLen ? saltLen : sizeof(zeroSalt);

  uint8_t prk[32];
  hmacSha256(actualSalt, actualSaltLen, ikm, ikmLen, prk);

  uint8_t t[32];
  size_t tLen = 0;
  size_t pos = 0;
  uint8_t block = 1;

  while (pos < outLen) {
    SHA256 sha;
    sha.resetHMAC(prk, sizeof(prk));
    if (tLen) sha.update(t, tLen);
    if (info && infoLen) sha.update(info, infoLen);
    sha.update(&block, 1);
    sha.finalizeHMAC(prk, sizeof(prk), t, sizeof(t));
    tLen = sizeof(t);

    size_t copyLen = min((size_t)32, outLen - pos);
    memcpy(out + pos, t, copyLen);
    pos += copyLen;
    block++;
  }

  secureWipe(prk);
  secureWipe(t);
  return true;
}

// --------------------- AES-256-GCM --------------------------

static void makeIv(const uint8_t seed[8], uint32_t counter, uint8_t iv[12]) {
  memcpy(iv, seed, 8);
  writeU32BE(iv + 8, counter);
}

static bool gcmEncrypt(const uint8_t key[32], const uint8_t iv[12],
                       uint32_t counter,
                       const uint8_t *plain, size_t plainLen,
                       uint8_t *cipherAndTag, size_t &outLen) {
  if (plainLen > MAX_PLAINTEXT) return false;

  GCM<AES256> gcm;
  if (!gcm.setKey(key, 32)) return false;
  if (!gcm.setIV(iv, 12)) return false;

  uint8_t aad[4];
  writeU32BE(aad, counter);
  gcm.addAuthData(aad, sizeof(aad));

  gcm.encrypt(cipherAndTag, plain, plainLen);
  gcm.computeTag(cipherAndTag + plainLen, GCM_TAG_LEN);
  outLen = plainLen + GCM_TAG_LEN;
  gcm.clear();
  return true;
}

static bool gcmDecrypt(const uint8_t key[32], const uint8_t iv[12],
                       uint32_t counter,
                       const uint8_t *cipherAndTag, size_t cipherAndTagLen,
                       uint8_t *plain, size_t &plainLen) {
  if (cipherAndTagLen < GCM_TAG_LEN) return false;
  size_t cipherLen = cipherAndTagLen - GCM_TAG_LEN;
  if (cipherLen > MAX_PLAINTEXT) return false;

  GCM<AES256> gcm;
  if (!gcm.setKey(key, 32)) return false;
  if (!gcm.setIV(iv, 12)) return false;

  uint8_t aad[4];
  writeU32BE(aad, counter);
  gcm.addAuthData(aad, sizeof(aad));

  gcm.decrypt(plain, cipherAndTag, cipherLen);
  bool ok = gcm.checkTag(cipherAndTag + cipherLen, GCM_TAG_LEN);
  gcm.clear();

  if (!ok) return false;
  plainLen = cipherLen;
  return true;
}

// ------------------------ HANDSHAKE -------------------------

/*
  SERVER_HELLO:
    type(1) version(1) Ns(32) Ps(64)

  CLIENT_HELLO:
    type(1) version(1) Nc(32) Pc(64)
    macC = HMAC(PSK, "C" || version || Ns || Ps || Nc || Pc)

  SERVER_FINISH:
    type(1)
    macS = HMAC(PSK, "S" || version || Ns || Ps || Nc || Pc)

  This authenticates both ephemeral public keys and both nonces using the PSK.
*/

static void buildTranscript(uint8_t role,
                            const uint8_t Ns[32], const uint8_t Ps[64],
                            const uint8_t Nc[32], const uint8_t Pc[64],
                            uint8_t *out, size_t &outLen) {
  size_t p = 0;
  out[p++] = role;
  out[p++] = VERSION;
  memcpy(out + p, Ns, 32); p += 32;
  memcpy(out + p, Ps, 64); p += 64;
  memcpy(out + p, Nc, 32); p += 32;
  memcpy(out + p, Pc, 64); p += 64;
  outLen = p;
}

static bool doHandshake() {
  secureChannelReady = false;
  sendCounter = recvCounter = 0;

  uint8_t header[2];
  if (!readExact(client, header, sizeof(header))) return false;
  if (header[0] != HS_SERVER_HELLO || header[1] != VERSION) { //dati iniziali usati dall'imlpementazione, non rilevanti
    Serial.println("[HS] Bad server hello");
    return false;
  }
//Ns= nonce server
  uint8_t Ns[32], Ps[64]; //ps[0..31] e ps[32...63] sono le coordinate XY
  // del punto della curva ellittica che rappresenta la chiave pubblica
  if (!readExact(client, Ns, sizeof(Ns))) return false;
  if (!readExact(client, Ps, sizeof(Ps))) return false;

  const uECC_Curve curve = uECC_secp256r1(); //richiede a uECC la curva p256, sostanzialmente una struttura
  // che definisce matematicamente i punti ammissibili 
  if (!uECC_valid_public_key(Ps, curve)) { //verifica che Ps sia punto ammissibile sulla curva p256
    Serial.println("[HS] Invalid server ECDH public key");
    return false;
  }

  uint8_t Pc[64], privC[32], Nc[32];
  if (!fillRandom(Nc, sizeof(Nc))) return false;

  if (!uECC_make_key(Pc, privC, curve)) { //crea chiave privata e corrispondente pubblica ECDH
    Serial.println("[HS] ECDH key generation failed");
    return false;
  }

  uint8_t transcript[1 + 1 + 32 + 64 + 32 + 64];
  size_t transcriptLen = 0;
  buildTranscript('C', Ns, Ps, Nc, Pc, transcript, transcriptLen);

  uint8_t macC[32];
  hmacSha256(PSK, sizeof(PSK), transcript, transcriptLen, macC);

  uint8_t helloPrefix[2] = {HS_CLIENT_HELLO, VERSION};
  if (!writeExact(client, helloPrefix, sizeof(helloPrefix))) return false;
  if (!writeExact(client, Nc, sizeof(Nc))) return false;
  if (!writeExact(client, Pc, sizeof(Pc))) return false;
  if (!writeExact(client, macC, sizeof(macC))) return false;

  uint8_t finishType;
  if (!readExact(client, &finishType, 1)) return false;
  if (finishType != HS_SERVER_FINISH) return false;

  uint8_t receivedMacS[32];
  if (!readExact(client, receivedMacS, sizeof(receivedMacS))) return false;

  buildTranscript('S', Ns, Ps, Nc, Pc, transcript, transcriptLen);
  uint8_t expectedMacS[32];
  hmacSha256(PSK, sizeof(PSK), transcript, transcriptLen, expectedMacS);

  if (!constTimeEq(receivedMacS, expectedMacS, 32)) {
    Serial.println("[HS] Server PSK authentication failed");
    secureWipe(privC);
    return false;
  }

  uint8_t sharedSecret[32];
  if (!uECC_shared_secret(Ps, privC, sharedSecret, curve)) {
    Serial.println("[HS] ECDH failed");
    secureWipe(privC);
    return false;
  }

  // Salt binds key derivation to this exact handshake.
  uint8_t salt[64];
  memcpy(salt, Ns, 32);
  memcpy(salt + 32, Nc, 32);

  static const uint8_t INFO[] = "esp8266-psk-ecdh-v1";
  uint8_t material[80];
  if (!hkdfSha256(sharedSecret, sizeof(sharedSecret),
                  salt, sizeof(salt),
                  INFO, sizeof(INFO) - 1,
                  material, sizeof(material))) {
    secureWipe(privC);
    secureWipe(sharedSecret);
    return false;
  }

  // Server -> ESP: first 40 bytes.
  memcpy(recvKey, material, 32);
  memcpy(recvIvSeed, material + 32, 8);

  // ESP -> Server: next 40 bytes.
  memcpy(sendKey, material + 40, 32);
  memcpy(sendIvSeed, material + 72, 8);

  secureWipe(privC);
  secureWipe(sharedSecret);
  secureWipe(material);
  secureWipe(macC);
  secureWipe(expectedMacS);

  secureChannelReady = true;
  Serial.println("[HS] Secure channel established");
  return true;
}

// ---------------------- SECURE FRAMES -----------------------

/*
  Secure frame:
    type(1) = 0x20
    counter(4, big-endian)         -- plaintext but authenticated as GCM AAD
    ciphertext_length(2, BE)
    ciphertext || GCM_tag(16)

  IV = direction-specific 8-byte seed || 4-byte counter
*/

static bool sendSecureText(const String &text) {
  if (!secureChannelReady || !client.connected()) return false;
  if (text.length() > MAX_PLAINTEXT) return false;
  if (sendCounter == 0xFFFFFFFFUL) {
    Serial.println("[SEC] Counter exhausted; reconnect required");
    return false;
  }

  uint32_t counter = ++sendCounter;
  uint8_t iv[12];
  makeIv(sendIvSeed, counter, iv);

  uint8_t cipher[MAX_CIPHERTEXT];
  size_t cipherLen = 0;
  if (!gcmEncrypt(sendKey, iv, counter,
                  (const uint8_t *)text.c_str(), text.length(),
                  cipher, cipherLen)) {
    return false;
  }

  uint8_t hdr[7];
  hdr[0] = FRAME_SECURE;
  writeU32BE(hdr + 1, counter);
  writeU16BE(hdr + 5, (uint16_t)cipherLen);

  return writeExact(client, hdr, sizeof(hdr)) &&
         writeExact(client, cipher, cipherLen);
}

static bool receiveSecureText(String &outText, uint32_t timeoutMs = 20) {
  outText = "";
  unsigned long start = millis();

  while (client.connected() && client.available() < 7) {
    if (millis() - start >= timeoutMs) return false;
    delay(1);
    yield();
  }
  if (client.available() < 7) return false;

  uint8_t hdr[7];
  if (!readExact(client, hdr, sizeof(hdr))) return false;
  if (hdr[0] != FRAME_SECURE) {
    Serial.println("[SEC] Unexpected frame type");
    return false;
  }

  uint32_t counter = readU32BE(hdr + 1);
  uint16_t cipherLen = readU16BE(hdr + 5);

  if (counter <= recvCounter) {
    Serial.println("[SEC] Replay/out-of-order packet rejected");
    return false;
  }
  if (cipherLen < GCM_TAG_LEN || cipherLen > MAX_CIPHERTEXT) {
    Serial.println("[SEC] Invalid ciphertext length");
    return false;
  }

  uint8_t cipher[MAX_CIPHERTEXT];
  if (!readExact(client, cipher, cipherLen)) return false;

  uint8_t iv[12];
  makeIv(recvIvSeed, counter, iv);

  uint8_t plain[MAX_PLAINTEXT + 1];
  size_t plainLen = 0;
  if (!gcmDecrypt(recvKey, iv, counter, cipher, cipherLen, plain, plainLen)) {
    Serial.println("[SEC] Authentication/decryption failed");
    return false;
  }

  recvCounter = counter;
  plain[plainLen] = '\0';
  outText = String((char *)plain);
  return true;
}

// --------------------- APPLICATION LOGIC --------------------

static String currentTimeString() {
  time_t now = time(nullptr);
  if (now < 100000) {
    return String("UNSYNCED");
  }
  struct tm localTm;
  localtime_r(&now, &localTm);
  char buf[16];
  strftime(buf, sizeof(buf), "%H:%M:%S", &localTm);
  return String(buf);
}

static void processCommand(const String &cmd) {
  if (cmd.startsWith("INC|")) {
    uint32_t n = (uint32_t)cmd.substring(4).toInt();
    if (n == 0) n = 1;
    intervalSeconds = min(MAX_INTERVAL, intervalSeconds + n);
    sendSecureText("INTERVAL|" + String(intervalSeconds));
  } else if (cmd.startsWith("DEC|")) {
    uint32_t n = (uint32_t)cmd.substring(4).toInt();
    if (n == 0) n = 1;
    if (n >= intervalSeconds) intervalSeconds = MIN_INTERVAL;
    else intervalSeconds -= n;
    if (intervalSeconds < MIN_INTERVAL) intervalSeconds = MIN_INTERVAL;
    sendSecureText("INTERVAL|" + String(intervalSeconds));
  } else if (cmd.startsWith("SET|")) {
    uint32_t n = (uint32_t)cmd.substring(4).toInt();
    intervalSeconds = constrain(n, MIN_INTERVAL, MAX_INTERVAL);
    sendSecureText("INTERVAL|" + String(intervalSeconds));
  } else if (cmd == "GET") {
    sendSecureText("INTERVAL|" + String(intervalSeconds));
  } else {
    sendSecureText("ERROR|UNKNOWN_COMMAND");
  }
}

static void connectWifi() {
  WiFi.mode(WIFI_STA);
  //rimosso  WiFi.begin(WIFI_SSID, WIFI_PASSWORD);

  WiFi.begin(WIFI_SSID);
  Serial.print("[WIFI] Connecting");
  while (WiFi.status() != WL_CONNECTED) {
    delay(500);
    Serial.print(".");
  }
  Serial.println();
  Serial.print("[WIFI] IP: ");
  Serial.println(WiFi.localIP());
}

static void syncClock() {
  configTime(0, 0, NTP_1, NTP_2);
  setenv("TZ", TZ_INFO, 1);
  tzset();

  Serial.print("[NTP] Synchronizing");
  unsigned long start = millis();
  while (time(nullptr) < 100000 && millis() - start < 15000) {
    delay(250);
    Serial.print(".");
  }
  Serial.println();
  Serial.print("[NTP] Time: ");
  Serial.println(currentTimeString());
}

static bool connectServerAndHandshake() {
  Serial.print("[TCP] Connecting to ");
  Serial.print(SERVER_IP);
  Serial.print(":");
  Serial.println(SERVER_PORT);

  if (!client.connect(SERVER_IP, SERVER_PORT)) {
    Serial.println("[TCP] Connection failed");
    return false;
  }
  client.setNoDelay(true);

  if (!doHandshake()) {
    Serial.println("[HS] Handshake failed");
    client.stop();
    return false;
  }

  lastSendMs = millis() - intervalSeconds * 1000UL; // send immediately
  return true;
}

// --------------------------- SETUP ---------------------------

void setup() {
  Serial.begin(115200);
  delay(50);

  uECC_set_rng(&microEccRng); 
  //fornisce alla libreria micro-ecc una funzione per generare numeri casuali(usato da uECC_make_key).
  //os_get_random e' una fonte TRNG, poiche' usa il rumore dell'ambiente catturato dal sistema wifi

  connectWifi();
  syncClock(); //crittograficamente non sicuro, si potrebbe utilizzare NTS (network time security) oppure 
  //fare in modo che il server invii l'orario del suo orologio interno all'esp
}

// ---------------------------- LOOP ---------------------------

void loop() {
  if (WiFi.status() != WL_CONNECTED) {
    secureChannelReady = false;
    client.stop();
    connectWifi();
  }

  if (!client.connected() || !secureChannelReady) {
    secureChannelReady = false;
    client.stop();
    if (!connectServerAndHandshake()) { //handshake crittografico
      delay(2000);
      return;
    }
  }

  // Receive PC commands.
  String cmd;
  while (client.available() >= 7) {
    if (receiveSecureText(cmd, 1000)) {
      Serial.print("[RX] ");
      Serial.println(cmd);
      processCommand(cmd);
    } else {
      break;
    }
  }

  // Periodic time message.
  unsigned long nowMs = millis();
  if (nowMs - lastSendMs >= intervalSeconds * 1000UL) {
    String msg = "TIME|" + currentTimeString();
    if (sendSecureText(msg)) {
      Serial.print("[TX] ");
      Serial.print(msg);
      Serial.print(" (X=");
      Serial.print(intervalSeconds);
      Serial.println("s)");
    } else {
      secureChannelReady = false;
      client.stop();
    }
    lastSendMs = nowMs;
  }

  delay(5);
  yield();
}
