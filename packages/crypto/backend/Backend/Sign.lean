import Backend.Error
import Backend.Sized

/-!
# Key agreement and signatures

The bindings of `c/p2pcrypto.c` for X25519 (RFC 7748), Ed25519
(RFC 8032), RSA (RSASSA-PKCS1-v1_5 with SHA-256, RFC 8017 §8.2),
secp256k1, and ECDSA P-256 (both ECDSA with SHA-256, SEC 1). Root ARCHITECTURE §4.6 routes P-256 verification to the
etheorem package `LeanHazmatP256`. That package binds verification
only, so P-256 signing and public-key derivation come from here. All
of secp256k1 stays here. The etheorem verifier accepts a high S, and
§4.6 requires a low S (the package PLAN, "Pin outcomes").

**Key forms.** A key crosses as opaque bytes.
- Ed25519 and X25519 take the raw 32-byte keys.
- secp256k1 takes the raw 32-byte scalar and gives the 33-byte
  compressed SEC1 point.
- RSA and P-256 take the private key in its type-specific DER form
  (PKCS#1 `RSAPrivateKey`, SEC1 `ECPrivateKey`). They give the public
  key as SubjectPublicKeyInfo DER.

The caller chooses which form a protocol stores. This package exposes
no marshaling of its own (package ARCHITECTURE, "Decisions").

**Binding types (§3.6).** Ed25519 and RSASSA-PKCS1-v1_5 sign
deterministically, and every derivation and verifier is deterministic,
so those bindings are pure. Both secp256k1 signers derive the nonce
by RFC 6979, so they are pure too. The shim keeps that promise. The
same input gives the same output, and the call reads no global state
and has no side effect. The P-256 signer draws a random nonce, so it
takes the world. The key generators take it too.

**The ownership rule.** The shim borrows every `ByteArray` argument of
an `@[extern]` declaration below. The declaration marks it `@&`, and
the shim declares it `b_lean_obj_arg` and never takes a reference
(contract 1).

**Verifier strictness (§4.6).** A verifier accepts only the key type
and size it claims.
- The RSA verifier rejects a non-RSA key and a key outside 2048 to 8192
  bits.
- The P-256 verifier rejects any key off the P-256 curve.
- The secp256k1 verifier rejects a high S and a non-canonical DER
  signature.

The checks read the parsed key, so they live in the C verifier
(contract 2).

**The verifier fold.** A verifier returns `Bool`. `false` covers a
signature that does not verify, every malformed input, and every
library fault, fail-closed. The `Bool` has no fault channel (§3.6).

**Trust boundary.** The declarations are `opaque`. `#print axioms` does
not list an `opaque` constant, so this docstring is the record of the
assumption. The library is the toolchain's bundled static OpenSSL 3,
which `lean-toolchain` pins, as in `Backend.Sym`. `Tests/Backend.lean`
pins the bindings by the RFC 8032 and RFC 7748 vectors and the captured
go key fixtures. The go signer uses the RFC 6979 nonce too, so the go
secp256k1 fixture pins both secp256k1 signers byte for byte.
`Tests/BackendStrict.lean` pins the verifier strictness, the
determinism, and key generation. The raw declarations
are `private`, because the shim trusts the sizes the wrappers check.
This docstring is their trust note.
-/

set_option autoImplicit false

namespace Backend

/-- A shim answer that must be exactly 32 bytes, as a `Key32`. A wrong
size is a library fault. The shim checks the length it writes. -/
private def toKey32 (b : ByteArray) : Except CryptoError Key32 :=
  match Key32.ofByteArray? b with
  | some k => .ok k
  | none => .error .fault

/-! ## X25519 -/

@[extern "leanp2p_x25519_public"]
private opaque x25519PublicRaw (priv : @& ByteArray) : Option ByteArray

@[extern "leanp2p_x25519_dh"]
private opaque x25519Raw (priv : @& ByteArray) (peer : @& ByteArray) : Option ByteArray

/-- The X25519 public key of a private key (RFC 7748 §6.1). Every
32-byte string is a valid private key, so `fault` is the only failure. -/
def x25519PublicKey (priv : Key32) : Except CryptoError Key32 :=
  liftShim .fault (x25519PublicRaw priv.bytes) >>= toKey32

/-- The X25519 shared secret of a private key and a peer's public key.
A peer key of small order gives the all-zero secret, which RFC 7748
§6.1 lets a protocol reject. OpenSSL rejects it, and the binding
reports `invalidKey`. -/
def x25519 (priv peer : Key32) : Except CryptoError Key32 :=
  liftShim .invalidKey (x25519Raw priv.bytes peer.bytes) >>= toKey32

/-! ## Ed25519 -/

@[extern "leanp2p_ed25519_public"]
private opaque ed25519PublicRaw (seed : @& ByteArray) : Option ByteArray

@[extern "leanp2p_ed25519_sign"]
private opaque ed25519SignRaw (seed : @& ByteArray) (msg : @& ByteArray) : Option ByteArray

@[extern "leanp2p_ed25519_verify"]
private opaque ed25519VerifyRaw (pub : @& ByteArray) (msg : @& ByteArray)
    (sig : @& ByteArray) : Bool

@[extern "leanp2p_ed25519_sig_len"]
private opaque ed25519SigLenRaw : Unit → UInt32

/-- The Ed25519 signature length (RFC 8032 §5.1.6), 64 bytes. The
shim's `ED25519_SIG_LEN` is the one home of the number, and this name
reads it, as `rsaMinBits` reads the RSA range. -/
def ed25519SigLen : Nat := (ed25519SigLenRaw ()).toNat

/-- The Ed25519 public key of a 32-byte seed (RFC 8032 §5.1.5). Every
seed is valid, so `fault` is the only failure. -/
def ed25519PublicKey (seed : Key32) : Except CryptoError Key32 :=
  liftShim .fault (ed25519PublicRaw seed.bytes) >>= toKey32

/-- The 64-byte Ed25519 signature of `msg` (RFC 8032 §5.1.6). Signing is
deterministic, so the binding is pure. -/
def ed25519Sign (seed : Key32) (msg : ByteArray) : Except CryptoError ByteArray :=
  liftShim .fault (ed25519SignRaw seed.bytes msg)

/-- Verify an Ed25519 signature (RFC 8032 §5.1.7). These inputs give
`false`: a public key or a signature of the wrong size, a point that
does not decode, and a signature that does not verify. -/
def ed25519Verify (pub msg sig : ByteArray) : Bool :=
  match Key32.ofByteArray? pub with
  | some k => sig.size == ed25519SigLen && ed25519VerifyRaw k.bytes msg sig
  | none => false

/-! ## RSA -/

@[extern "leanp2p_rsa_public"]
private opaque rsaPublicRaw (priv : @& ByteArray) : Option ByteArray

@[extern "leanp2p_rsa_sign"]
private opaque rsaSignRaw (priv : @& ByteArray) (msg : @& ByteArray) : Option ByteArray

@[extern "leanp2p_rsa_verify"]
private opaque rsaVerifyRaw (spki : @& ByteArray) (msg : @& ByteArray)
    (sig : @& ByteArray) : Bool

@[extern "leanp2p_rsa_pkcs1"]
private opaque rsaPkcs1Raw (priv : @& ByteArray) : Option ByteArray

/-- The SPKI DER public key of a PKCS#1 DER private key. A key that does
not parse, or one outside 2048 to 8192 bits, is `invalidKey`. -/
def rsaPublicKey (priv : ByteArray) : Except CryptoError ByteArray :=
  liftShim .invalidKey (rsaPublicRaw priv)

/-- The PKCS#1 DER of a DER private key, from either form the loader
reads (PKCS#1 or PKCS#8). The output depends on the key alone, so a
caller that stores it holds one form per key. The key rules of
`rsaPublicKey` apply. -/
def rsaPkcs1 (priv : ByteArray) : Except CryptoError ByteArray :=
  liftShim .invalidKey (rsaPkcs1Raw priv)

/-- The RSASSA-PKCS1-v1_5 SHA-256 signature of `msg`. The padding draws
no randomness, so signing is deterministic and the binding is pure.
The key rules of `rsaPublicKey` apply. -/
def rsaSign (priv msg : ByteArray) : Except CryptoError ByteArray :=
  liftShim .invalidKey (rsaSignRaw priv msg)

/-- Verify an RSASSA-PKCS1-v1_5 SHA-256 signature under an SPKI DER
public key. A non-RSA key and an RSA key outside 2048 to 8192 bits give
`false`, as does every malformed input. -/
def rsaVerify (spki msg sig : ByteArray) : Bool := rsaVerifyRaw spki msg sig

/-! ## ECDSA P-256

Signing and public-key derivation stay here. The facade routes
verification to `LeanHazmatP256` (root ARCHITECTURE §4.6). The verifier
here is the reference of the route's differential test, and one facade
line restores the route to it. -/

@[extern "leanp2p_p256_public"]
private opaque p256PublicRaw (priv : @& ByteArray) : Option ByteArray

@[extern "leanp2p_p256_sign"]
private opaque p256SignRaw (priv : @& ByteArray) (msg : @& ByteArray) : IO (Option ByteArray)

@[extern "leanp2p_p256_verify"]
private opaque p256VerifyRaw (spki : @& ByteArray) (msg : @& ByteArray)
    (sig : @& ByteArray) : Bool

@[extern "leanp2p_p256_sec1"]
private opaque p256Sec1Raw (priv : @& ByteArray) : Option ByteArray

/-- The SPKI DER public key of a SEC1 DER P-256 private key. A key that
does not parse, or a key on another curve, is `invalidKey`. -/
def p256PublicKey (priv : ByteArray) : Except CryptoError ByteArray :=
  liftShim .invalidKey (p256PublicRaw priv)

/-- The SEC1 DER of a DER P-256 private key, from either form the loader
reads (SEC1 or PKCS#8). The output depends on the key alone, so a caller
that stores it holds one form per key. A key that does not parse, or a
key on another curve, is `invalidKey`. -/
def p256Sec1 (priv : ByteArray) : Except CryptoError ByteArray :=
  liftShim .invalidKey (p256Sec1Raw priv)

/-- The DER ECDSA signature of SHA-256(`msg`). The nonce is random, so
two calls give different signatures, and both verify. -/
def p256Sign (priv msg : ByteArray) : ExceptT CryptoError IO ByteArray := do
  ExceptT.mk (liftShim .invalidKey <$> p256SignRaw priv msg)

/-- The 27-byte head of the SPKI DER of an uncompressed P-256 point
(RFC 5480 §2): `SEQUENCE(89) { SEQUENCE(19) { OID id-ecPublicKey, OID
prime256v1 }, BIT STRING(66) 0x00 0x04 … }`. The `0x00` counts the
unused bits of the BIT STRING, and `0x04` tags the point as
uncompressed (SEC 1 §2.3.3). This is the one home of the layout. The
facade's P-256 route (unit 2 of the package PLAN) reads it from here. -/
def p256SpkiHead : ByteArray := ByteArray.mk #[
  0x30, 0x59, 0x30, 0x13,
  0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01,
  0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07,
  0x03, 0x42, 0x00, 0x04]

/-- The size of one P-256 coordinate or scalar, 32 bytes. -/
def p256FieldSize : Nat := 32

/-- The size of the whole SPKI: the head, then the two coordinates. -/
def p256SpkiSize : Nat := p256SpkiHead.size + 2 * p256FieldSize

/-- True when `spki` is the SPKI DER of an uncompressed P-256 point, the
one form Go's `crypto/x509` accepts (`ecdsa.ParseUncompressedPublicKey`).
OpenSSL also loads the compressed and hybrid forms, so the verifier
checks the form here, before the shim runs. Whether the point lies on
the curve is the shim's check. -/
def p256SpkiUncompressed (spki : ByteArray) : Bool :=
  spki.size == p256SpkiSize && spki.extract 0 p256SpkiHead.size == p256SpkiHead

/-- Verify a DER ECDSA signature over SHA-256(`msg`) under an SPKI DER
public key. The key must pass `p256SpkiUncompressed`. A compressed or
hybrid point, a key off the P-256 curve, and every malformed input give
`false`. -/
def p256Verify (spki msg sig : ByteArray) : Bool :=
  p256SpkiUncompressed spki && p256VerifyRaw spki msg sig

/-! ## secp256k1

The etheorem verifier accepts a high S, so all of secp256k1 stays on
this shim (root ARCHITECTURE §4.6). -/

@[extern "leanp2p_secp256k1_public"]
private opaque secp256k1PublicRaw (scalar : @& ByteArray) : Option ByteArray

@[extern "leanp2p_secp256k1_sign"]
private opaque secp256k1SignRaw (scalar : @& ByteArray) (msg : @& ByteArray) : Option ByteArray

@[extern "leanp2p_secp256k1_sign_digest"]
private opaque secp256k1SignDigestRaw (scalar : @& ByteArray) (digest : @& ByteArray) :
    Option ByteArray

@[extern "leanp2p_secp256k1_verify"]
private opaque secp256k1VerifyRaw (point : @& ByteArray) (msg : @& ByteArray)
    (sig : @& ByteArray) : Bool

/-- `true` when `point` is a SEC1 point on secp256k1, compressed or
uncompressed. `false` for a point off the curve and every malformed
input, fail-closed. Trust: the toolchain's OpenSSL 3 loads and checks
the point. `Tests/Backend.lean` pins it with the go fixture key. -/
@[extern "leanp2p_secp256k1_check"]
opaque secp256k1PointValid (point : @& ByteArray) : Bool

/-- The 33-byte compressed SEC1 public point of a raw 32-byte scalar. A
scalar of zero, or one not below the group order, is `invalidKey`. -/
def secp256k1PublicKey (scalar : Key32) : Except CryptoError ByteArray :=
  liftShim .invalidKey (secp256k1PublicRaw scalar.bytes)

/-- The DER ECDSA signature of SHA-256(`msg`), the form of the peer-ids
spec, with S in its low form, so the signature passes the low-S rule
of `secp256k1Verify`. The shim signs through the same RFC 6979 core as
`secp256k1SignDigest`, so the binding is pure, and it reproduces the
go fixture signature byte for byte. A scalar of zero, or one not below
the group order, is `invalidKey`. -/
def secp256k1Sign (scalar : Key32) (msg : ByteArray) : Except CryptoError ByteArray :=
  liftShim .invalidKey (secp256k1SignRaw scalar.bytes msg)

/-- The 64-byte compact ECDSA signature `r ‖ s` of a 32-byte digest,
with S in its low form. The signer does not hash: the caller passes
the digest its protocol fixes, such as keccak-256 for the `v4` ENR
identity scheme (EIP-778). Each half is big-endian and left-padded to
32 bytes.

The nonce comes from RFC 6979 with HMAC-SHA-256, as in libsecp256k1
and decred, so one key and one digest give one signature, and the
binding is pure. The scalar rule of `secp256k1Sign` applies. The
compact form carries no recovery id. -/
def secp256k1SignDigest (scalar : Key32) (digest : Digest32) : Except CryptoError ByteArray :=
  liftShim .invalidKey (secp256k1SignDigestRaw scalar.bytes digest.bytes)

/-- Verify a DER ECDSA signature over SHA-256(`msg`) under a SEC1 point,
compressed or uncompressed. A high S, a non-canonical DER encoding, a
point off the curve, and every malformed input give `false`. -/
def secp256k1Verify (point msg sig : ByteArray) : Bool := secp256k1VerifyRaw point msg sig

/-! ## Key generation

Fresh private keys from the OpenSSL DRBG, in the form the bindings
above take, so a new key feeds straight into derive, sign, and verify.
Generation draws randomness, so every generator is `IO` (§3.6). A
library failure is `fault`. -/

@[extern "leanp2p_ed25519_generate"]
private opaque ed25519GenerateRaw : IO (Option ByteArray)

@[extern "leanp2p_x25519_generate"]
private opaque x25519GenerateRaw : IO (Option ByteArray)

@[extern "leanp2p_secp256k1_generate"]
private opaque secp256k1GenerateRaw : IO (Option ByteArray)

@[extern "leanp2p_p256_generate"]
private opaque p256GenerateRaw : IO (Option ByteArray)

@[extern "leanp2p_rsa_generate"]
private opaque rsaGenerateRaw (bits : USize) : IO (Option ByteArray)

/-- A generator's answer as a `Key32`. -/
private def generate32 (raw : IO (Option ByteArray)) : ExceptT CryptoError IO Key32 := do
  let b ← ExceptT.mk (liftShim .fault <$> raw)
  ExceptT.mk (pure (toKey32 b))

/-- A fresh Ed25519 seed. -/
def ed25519Generate : ExceptT CryptoError IO Key32 := generate32 ed25519GenerateRaw

/-- A fresh X25519 private key. -/
def x25519Generate : ExceptT CryptoError IO Key32 := generate32 x25519GenerateRaw

/-- A fresh secp256k1 scalar, in `[1, n - 1]`. -/
def secp256k1Generate : ExceptT CryptoError IO Key32 := generate32 secp256k1GenerateRaw

/-- A fresh P-256 private key, as SEC1 `ECPrivateKey` DER. -/
def p256Generate : ExceptT CryptoError IO ByteArray :=
  ExceptT.mk (liftShim .fault <$> p256GenerateRaw)

@[extern "leanp2p_rsa_min_bits"]
private opaque rsaMinBitsRaw : Unit → UInt32

@[extern "leanp2p_rsa_max_bits"]
private opaque rsaMaxBitsRaw : Unit → UInt32

/-- The smallest RSA modulus this package accepts, in bits (§4.6). The C
verifier checks the size of a parsed key, which this side cannot see.
So the shim's `RSA_MIN_BITS` is the one home of the number, and this
name reads it. -/
def rsaMinBits : Nat := (rsaMinBitsRaw ()).toNat

/-- The largest RSA modulus this package accepts, in bits (§4.6), read
from the shim's `RSA_MAX_BITS`, as `rsaMinBits` is. -/
def rsaMaxBits : Nat := (rsaMaxBitsRaw ()).toNat

/-- A fresh RSA private key of `bits` bits, as PKCS#1 `RSAPrivateKey`
DER. A size outside `rsaMinBits` to `rsaMaxBits` is `invalidInput`,
since the verifiers would reject the key. -/
def rsaGenerate (bits : Nat) : ExceptT CryptoError IO ByteArray := do
  if bits < rsaMinBits || bits > rsaMaxBits then throw .invalidInput
  ExceptT.mk (liftShim .fault <$> rsaGenerateRaw bits.toUSize)

end Backend
