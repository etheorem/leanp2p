import Backend.Error
import Backend.Sized

/-!
# Symmetric primitives and randomness

The bindings of `c/p2pcrypto.c` for random bytes, the SHA-1, SHA-256,
and SHA-512 digests, HMAC-SHA-256, HKDF-SHA-256 (RFC 5869), and
ChaCha20-Poly1305 (RFC 8439). SHA-256 here is the interim fallback for
the etheorem package `LeanHazmatSha256` (root ARCHITECTURE §4.6), and
the fallback is in force: the pin is out at the current etheorem rev
(the package PLAN, "Pin outcomes").

**The ownership rule.** Every `ByteArray` argument of an `@[extern]`
declaration below is borrowed (`@&`), and the shim declares it
`b_lean_obj_arg`. The shim reads it and never takes a reference. An
owned parameter leaks one reference per call (package ARCHITECTURE,
contract 1).

**Pure bindings.** Every primitive here except randomness is
deterministic, so its binding is a pure `opaque` declaration (§3.6).
That is a promise the shim keeps: the same input gives the same output,
and the call reads no global state and has no side effect. Lean may
share or reorder calls on that promise.

**Trust boundary.** The declarations are `opaque`, so the kernel knows
nothing of their values, and `#axioms` lists the assumption at every
use. The library is the static OpenSSL 3 `libcrypto.a` that the Lean
toolchain bundles and links into every executable, so `lean-toolchain`
pins it; the shim compiles against the system OpenSSL 3 headers (the
package `lakefile.lean`). The suite `Tests/Backend.lean` pins each
binding by vectors. The W3.3 cross-check (the package PLAN, unit 2)
compares the digests, HMAC, and HKDF with the pure copies of
`crypto/pure` at the IO edge.

The raw declarations are `private`. The shim trusts the sizes the Lean
side proves, so a raw call with a short key would read past the buffer.
Callers reach the shim only through the checked wrappers, and this
docstring is the trust note for every raw declaration below.
-/

set_option autoImplicit false

namespace Backend

/-! ## Randomness -/

/-- The most random bytes one call may ask for: 1 MiB. A larger draw is
a caller error, and the wrapper refuses it before the shim runs. -/
def maxRandomBytes : Nat := 1024 * 1024

@[extern "leanp2p_random_bytes"]
private opaque randomBytesRaw (n : USize) : IO ByteArray

/-- `n` bytes from the OpenSSL DRBG (`RAND_bytes`). A draw past
`maxRandomBytes` is `invalidInput`. A DRBG failure is a fault, and it
throws `IO.Error` (§3.5). -/
def randomBytes (n : Nat) : ExceptT CryptoError IO ByteArray := do
  if n > maxRandomBytes then throw .invalidInput
  randomBytesRaw n.toUSize

/-! ## Digests -/

@[extern "leanp2p_sha1"]
private opaque sha1Raw (data : @& ByteArray) : Option ByteArray

@[extern "leanp2p_sha256"]
private opaque sha256Raw (data : @& ByteArray) : Option ByteArray

@[extern "leanp2p_sha512"]
private opaque sha512Raw (data : @& ByteArray) : Option ByteArray

/-- SHA-1 (FIPS 180-4), 20 bytes. `fault` only if the library fails.
Pinned by the multihash spec vector and the empty-input digest; the
W3.3 cross-check (unit 2) compares it with `CryptoPure.Sha1`. -/
def sha1 (data : ByteArray) : Except CryptoError ByteArray := liftShim .fault (sha1Raw data)

/-- SHA-256 (FIPS 180-4), 32 bytes: the interim fallback for
`LeanHazmatSha256`. `fault` only if the library fails. -/
def sha256 (data : ByteArray) : Except CryptoError ByteArray := liftShim .fault (sha256Raw data)

/-- SHA-512 (FIPS 180-4), 64 bytes. `fault` only if the library fails. -/
def sha512 (data : ByteArray) : Except CryptoError ByteArray := liftShim .fault (sha512Raw data)

/-! ## HMAC and HKDF -/

@[extern "leanp2p_hmac_sha256"]
private opaque hmacSha256Raw (key : @& ByteArray) (data : @& ByteArray) : Option ByteArray

/-- HMAC-SHA-256 (RFC 2104), 32 bytes, for a key of any length. `fault`
only if the library fails. -/
def hmacSha256 (key data : ByteArray) : Except CryptoError ByteArray :=
  liftShim .fault (hmacSha256Raw key data)

/-- The longest HKDF-SHA-256 output: the block counter is one byte, so
255 blocks of 32 bytes (RFC 5869 §2.3). -/
def hkdfSha256MaxLen : Nat := 255 * 32

@[extern "leanp2p_hkdf_sha256"]
private opaque hkdfSha256Raw (salt : @& ByteArray) (ikm : @& ByteArray)
    (info : @& ByteArray) (len : USize) : Option ByteArray

/-- HKDF-SHA-256 extract then expand (RFC 5869 §2), `len` bytes of
output keying material. A `len` past `hkdfSha256MaxLen` is
`invalidInput`; an empty salt means 32 zero bytes, as the RFC says.
`len = 0` gives the empty output: RFC 5869 §2.3 allows it, and
OpenSSL's `EVP_KDF_derive` refuses a zero length, so the wrapper
answers before the shim runs. -/
def hkdfSha256 (salt ikm info : ByteArray) (len : Nat) : Except CryptoError ByteArray :=
  if len > hkdfSha256MaxLen then .error .invalidInput
  else if len == 0 then .ok .empty
  else liftShim .fault (hkdfSha256Raw salt ikm info len.toUSize)

/-! ## ChaCha20-Poly1305

The AEAD of RFC 8439 §2.8. A sealed message is the ciphertext followed
by the 16-byte Poly1305 tag. -/

/-- The Poly1305 tag length (RFC 8439 §2.8). -/
def aeadTagLen : Nat := 16

@[extern "leanp2p_chacha_seal"]
private opaque chachaSealRaw (key : @& ByteArray) (nonce : @& ByteArray) (ad : @& ByteArray)
    (pt : @& ByteArray) : Option ByteArray

@[extern "leanp2p_chacha_open"]
private opaque chachaOpenRaw (key : @& ByteArray) (nonce : @& ByteArray) (ad : @& ByteArray)
    (ct : @& ByteArray) : Option ByteArray

/-- Seal `pt` with associated data `ad`: the ciphertext and then the tag,
`pt.size + 16` bytes. `fault` only if the library fails, or for an
input past 2 GiB, which OpenSSL's `int` lengths cannot carry. Pinned by
the RFC 8439 §2.8.2 vector. -/
def chachaSeal (key : Key32) (nonce : Nonce12) (ad pt : ByteArray) :
    Except CryptoError ByteArray :=
  liftShim .fault (chachaSealRaw key.bytes nonce.bytes ad pt)

/-- Open a sealed message. A message shorter than the tag, or a tag that
does not verify, is `authFailed`, the one failure arm of this call. -/
def chachaOpen (key : Key32) (nonce : Nonce12) (ad ct : ByteArray) :
    Except CryptoError ByteArray :=
  if ct.size < aeadTagLen then .error .authFailed
  else liftShim .authFailed (chachaOpenRaw key.bytes nonce.bytes ad ct)

end Backend
