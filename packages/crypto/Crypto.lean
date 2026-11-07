import Backend
import LeanHazmatKeccak
import LeanHazmatSecp256k1
import Crypto.P256
import Crypto.Rng

/-!
# Crypto

The crypto facade, the one crypto import of every caller (root
ARCHITECTURE §3.6). Each line below names the production
implementation of one primitive, or of one family. The sources are
`crypto/backend`, the OpenSSL 3 shim, and three etheorem hazmat packages.
The facade ARCHITECTURE gives the reason for each route.

**The swap rule.** To move a primitive, change the right-hand side of
its line. Every name keeps the type of its source, so the new source
must fit that type, and no call site changes. `Tests/CryptoCross.lean`
demonstrates one swap.

**`export` and `abbrev`.** `export Backend (x)` inside `namespace
Crypto` makes `Crypto.x` an alias of `Backend.x`. The alias is a name
only: the declaration, its type, and its docstring stay at the source.
An `abbrev` states the type at the facade. The lines below use it
where the route differs from the backend, or where the backend binding
is an interim fallback. A reader of this file then sees the type that
a swap must fit.

The `Rng` seam (`Crypto.Rng`) and the P-256 route (`Crypto.P256`) live
in their own modules, and this file imports them.
-/

set_option autoImplicit false

namespace Crypto

/-! ## Types and errors -/

export Backend (CryptoError Key32 Digest32 Nonce12 Key32.ofByteArray?
  Digest32.ofByteArray? Nonce12.ofByteArray? Certificate Certificate.validAt)

/-! ## Randomness and key generation: the backend -/

export Backend (randomBytes maxRandomBytes
  ed25519Generate x25519Generate secp256k1Generate p256Generate rsaGenerate)

/-! ## Digests, MAC, and KDF -/

export Backend (sha1 sha512 hmacSha256 hkdfSha256 hkdfSha256MaxLen)

/-- SHA-256, 32 bytes: the backend binding. It is the interim fallback
while the `LeanHazmatSha256` pin is out (backend PLAN, "Pin
outcomes"). -/
abbrev sha256 : ByteArray → Except CryptoError ByteArray := Backend.sha256

/-- Keccak-256 with the original Keccak padding, 32 bytes: the etheorem
package `LeanHazmatKeccak`. -/
abbrev keccak256 : ByteArray → ByteArray := LeanHazmat.Keccak.keccak256

/-! ## AEAD and key agreement: the backend -/

export Backend (chachaSeal chachaOpen aeadTagLen aeadMaxLen x25519PublicKey x25519)

/-! ## Signatures -/

export Backend (ed25519PublicKey ed25519Sign ed25519Verify ed25519SigLen
  rsaPublicKey rsaPkcs1 rsaSign rsaVerify rsaMinBits rsaMaxBits
  p256PublicKey p256Sec1 p256Sign
  secp256k1PublicKey secp256k1PointValid secp256k1Sign secp256k1SignDigest
  secp256k1Verify)

/-- ECDSA P-256 verification over SHA-256(`msg`), with an SPKI DER key
and a DER signature: the etheorem package `LeanHazmatP256`, through
the adapter of `Crypto.P256`. -/
abbrev p256Verify : ByteArray → ByteArray → ByteArray → Bool := P256.verify

/-- secp256k1 key recovery: the 64-byte public key `x ‖ y` from a
32-byte hash, the 32-byte `r` and `s`, and a recovery id from 0 to 3.
An empty answer covers every failure. The etheorem package
`LeanHazmatSecp256k1` serves it (root ARCHITECTURE §4.6), and the
backend binds no recovery. The library accepts a high S here, so a
caller with a low-S rule checks S itself. -/
abbrev secp256k1Recover : ByteArray → ByteArray → ByteArray → UInt32 → ByteArray :=
  LeanHazmat.Secp256k1.ecdsaRecover

/-! ## X.509: the backend -/

export Backend (inspect selfSigned)

end Crypto
