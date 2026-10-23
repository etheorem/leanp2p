import LeanP2P.Crypto.Bytes
/-!
# Crypto backend (VECTOR_TEST_PLAN.md, phase 2 step 11)

Decision, recorded here and in the README: asymmetric crypto (Ed25519,
X25519, secp256k1, ECDSA P-256, RSA) binds to **OpenSSL 3** through a small
C shim (`c/p2pcrypto.c`) with `@[extern]` opaque declarations - the plan's
recommendation that constant-time implementations are not sensible to write
in Lean for a production node. libsodium was the other candidate but is not
available in this environment; OpenSSL covers Ed25519/X25519 and the DER /
SPKI marshaling the peer-ids spec requires. Key-derivation and MAC
primitives (SHA-256/SHA-512, HMAC-SHA256, HKDF-SHA256) exist in pure Lean
(`Crypto/Sha256`, `Crypto/Sha512`, `Crypto/Hmac`, `Crypto/Hkdf`); the
OpenSSL versions here are the cross-checks that anchor them at the IO edge.

Marshaling shapes follow the peer-ids spec and go-libp2p (vendored at
`vendor/go-libp2p`, see `keys-go-libp2p.json`): Ed25519 raw keys and
64-byte signatures; secp256k1 compressed points and BIP-62 low-S DER
signatures; ECDSA P-256 SEC1 or PKCS#8 private (auto-detected; go-libp2p
serializes SEC1) / SPKI public / DER signatures; RSA PKCS#1 private /
SPKI public / RSASSA-PKCS1-v1_5.
Signing and hashing of messages happen inside the backend where the
algorithm fixes them (SHA-256 for the DER schemes, none for Ed25519).

Every `ByteArray` argument is passed **borrowed** (`@&`): the shim declares
each one `b_lean_obj_arg` and never takes a reference, so an owned
parameter would leak a reference on every call.
-/

namespace LeanP2P.OpenSsl

/-- `randomBytes n`: `n` cryptographically secure random bytes (`none` on
backend failure; capped at 1 MiB by the shim). -/
@[extern "leanp2p_random_bytes"]
opaque randomBytes (n : @& USize) : IO (Option ByteArray)

/-- SHA-256 of a message (cross-check for the pure Lean implementation). -/
@[extern "leanp2p_sha256"]
opaque sha256 (msg : @& ByteArray) : IO (Option ByteArray)

/-- SHA-512 of a message (cross-check for the pure Lean implementation). -/
@[extern "leanp2p_sha512"]
opaque sha512 (msg : @& ByteArray) : IO (Option ByteArray)

/-- HMAC-SHA-256 (cross-check for the pure Lean implementation). -/
@[extern "leanp2p_hmac_sha256"]
opaque hmacSha256 (key msg : @& ByteArray) : IO (Option ByteArray)

/-- HKDF-SHA-256, extract-and-expand (cross-check for the pure Lean
implementation). -/
@[extern "leanp2p_hkdf_sha256"]
opaque hkdfSha256 (salt ikm info : @& ByteArray) (outLen : @& USize) :
    IO (Option ByteArray)

/-- `resolveV4 host`: the first IPv4 address of `host` via getaddrinfo
(4 bytes; the runtime has no DNS, and the interop harness must accept the
compose service name `redis`). -/
@[extern "leanp2p_resolve_v4"]
opaque resolveV4 (host : @& String) : IO (Option ByteArray)

/-! ## Ed25519 -/

/-- Public key (32 bytes) derived from the raw RFC 8032 seed. -/
@[extern "leanp2p_ed25519_pubkey"]
opaque ed25519Pubkey (seed : @& ByteArray) : IO (Option ByteArray)

/-- Ed25519 signature (64 bytes) of a message under the seed. -/
@[extern "leanp2p_ed25519_sign"]
opaque ed25519Sign (seed msg : @& ByteArray) : IO (Option ByteArray)

/-- Ed25519 verification (RFC 8032). -/
@[extern "leanp2p_ed25519_verify"]
opaque ed25519Verify (pub msg sig : @& ByteArray) : IO Bool

/-! ## X25519 -/

/-- X25519 public key (32 bytes) from the raw private scalar. -/
@[extern "leanp2p_x25519_pubkey"]
opaque x25519Pubkey (priv : @& ByteArray) : IO (Option ByteArray)

/-- X25519 Diffie-Hellman shared secret (32 bytes). -/
@[extern "leanp2p_x25519_dh"]
opaque x25519Dh (priv peerPub : @& ByteArray) : IO (Option ByteArray)

/-! ## secp256k1 -/

/-- 33-byte compressed public key from the 32-byte private scalar. -/
@[extern "leanp2p_secp256k1_pubkey"]
opaque secp256k1Pubkey (scalar : @& ByteArray) : IO (Option ByteArray)

/-- BIP-62 low-S DER signature over SHA-256(msg). -/
@[extern "leanp2p_secp256k1_sign"]
opaque secp256k1Sign (scalar msg : @& ByteArray) : IO (Option ByteArray)

/-- Verify a DER signature over SHA-256(msg) against a compressed key.
Enforces BIP-62 low-S, so the accepted signature set matches go-libp2p. -/
@[extern "leanp2p_secp256k1_verify"]
opaque secp256k1Verify (pub msg sig : @& ByteArray) : IO Bool

/-! ## ECDSA P-256 (SEC1/PKCS#8 private, SPKI public, DER signatures) -/

/-- SPKI (PKIX) DER public key derived from a SEC1 or PKCS#8 DER private
key. -/
@[extern "leanp2p_ecdsa_p256_priv_to_pub"]
opaque ecdsaP256PrivToPub (pkcs8 : @& ByteArray) : IO (Option ByteArray)

/-- DER signature over SHA-256(msg). -/
@[extern "leanp2p_ecdsa_p256_sign"]
opaque ecdsaP256Sign (pkcs8 msg : @& ByteArray) : IO (Option ByteArray)

/-- Verify a DER signature over SHA-256(msg) against an SPKI DER key.
The SPKI must carry a P-256 key. -/
@[extern "leanp2p_ecdsa_p256_verify"]
opaque ecdsaP256Verify (spki msg sig : @& ByteArray) : IO Bool

/-! ## RSA (PKCS#1 private, SPKI public, RSASSA-PKCS1-v1_5) -/

/-- SPKI (PKIX) DER public key from a PKCS#1 DER private key. -/
@[extern "leanp2p_rsa_priv_to_pub"]
opaque rsaPrivToPub (pkcs1 : @& ByteArray) : IO (Option ByteArray)

/-- RSASSA-PKCS1-v1_5 signature over SHA-256(msg). -/
@[extern "leanp2p_rsa_sign"]
opaque rsaSign (pkcs1 msg : @& ByteArray) : IO (Option ByteArray)

/-- Verify an RSASSA-PKCS1-v1_5 signature over SHA-256(msg) against an
SPKI DER key. The SPKI must carry an RSA key of 2048-8192 bits
(the libp2p security baseline). -/
@[extern "leanp2p_rsa_verify"]
opaque rsaVerify (spki msg sig : @& ByteArray) : IO Bool

/-! ## ChaCha20-Poly1305 (phase 3 step 16: the Noise cipher) -/

/-- AEAD seal: `ciphertext || 16-byte tag` under a 32-byte key and 12-byte
nonce (Noise builds it as 4 zero bytes ++ little-endian 64-bit counter). -/
@[extern "leanp2p_chacha20poly1305_seal"]
opaque chacha20poly1305Seal (key nonce ad plaintext : @& ByteArray) :
    IO (Option ByteArray)

/-- AEAD open of a `ciphertext || tag` buffer; `none` on authentication
failure. -/
@[extern "leanp2p_chacha20poly1305_open"]
opaque chacha20poly1305Open (key nonce ad ciphertext : @& ByteArray) :
    IO (Option ByteArray)

/-! ## X.509 libp2p certificate extension (phase 3 step 17: tls.md) -/

/-- The certificate's own SPKI DER plus the value of the libp2p extension
(OID 1.3.6.1.4.1.53594.1.1; the DER of the SignedKey structure), or `none`
when the certificate does not parse or lacks the extension. -/
@[extern "leanp2p_x509_libp2p_ext"]
opaque x509Libp2pExt (cert : @& ByteArray) :
    IO (Option (ByteArray × ByteArray))

/-- Does the certificate's signature verify under its own public key? The
tls.md vectors are self-signed certificates. -/
@[extern "leanp2p_x509_self_signed"]
opaque x509SelfSigned (cert : @& ByteArray) : IO Bool

end LeanP2P.OpenSsl
