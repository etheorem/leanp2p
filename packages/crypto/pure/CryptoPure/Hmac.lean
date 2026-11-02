import CryptoPure.Constants
import CryptoPure.Sha256
import CryptoPure.Sha512

/-!
# HMAC

RFC 2104 over the `List Nat` model. The construction takes the hash
and its block size as arguments, so HMAC over SHA-256 and HMAC over
SHA-512 are one function at two arguments. The theorems hold for any
hash whose output has a fixed length that fits in a block. This is the
audited copy, and the oracle of the W3.3 cross-check (ARCHITECTURE
§4.6); production HMAC is the backend binding behind the `Crypto`
facade.
-/

set_option autoImplicit false

namespace CryptoPure.Hmac

/-- The key as one block (RFC 2104 §2): a key longer than the block is
hashed first, and the result is padded with zero bytes to the block
size. -/
def normKey (hash : List Nat → List Nat) (blockSize : Nat) (key : List Nat) : List Nat :=
  let k := if key.length > blockSize then hash key else key
  k ++ List.replicate (blockSize - k.length) 0

/-- HMAC (RFC 2104 §2): `H(K ⊕ opad, H(K ⊕ ipad, text))`. -/
def hmac (hash : List Nat → List Nat) (blockSize : Nat) (key msg : List Nat) : List Nat :=
  let k := normKey hash blockSize key
  hash (k.map (· ^^^ opad) ++ hash (k.map (· ^^^ ipad) ++ msg))

/-- HMAC-SHA-256, the instance the vectors pin and HKDF uses. -/
def sha256 (key msg : List Nat) : List Nat :=
  hmac Sha256.digest Sha256.blockSize key msg

/-- HMAC-SHA-512. -/
def sha512 (key msg : List Nat) : List Nat :=
  hmac Sha512.digest Sha512.blockSize key msg

/-- The reduction: HMAC is the RFC 2104 formula over the hash. -/
theorem hmacEq (hash : List Nat → List Nat) (blockSize : Nat) (key msg : List Nat) :
    hmac hash blockSize key msg =
      hash ((normKey hash blockSize key).map (· ^^^ opad) ++
        hash ((normKey hash blockSize key).map (· ^^^ ipad) ++ msg)) :=
  rfl

/-- The normalized key fills exactly one block, when the hash output
fits in a block. -/
theorem lengthNormKey {hash : List Nat → List Nat} {blockSize : Nat}
    (hfit : ∀ m, (hash m).length ≤ blockSize) (key : List Nat) :
    (normKey hash blockSize key).length = blockSize := by
  unfold normKey
  split
  · have := hfit key
    simp
    omega
  · simp
    omega

/-- A key longer than the block gives the same MAC as its hash.
The hash output must fit in one block (RFC 2104 §2). -/
theorem hmacLongKey {hash : List Nat → List Nat} {blockSize : Nat}
    (hfit : ∀ m, (hash m).length ≤ blockSize) {key : List Nat}
    (hlong : blockSize < key.length) (msg : List Nat) :
    hmac hash blockSize key msg = hmac hash blockSize (hash key) msg := by
  have hfk := hfit key
  simp only [hmac, normKey, show key.length > blockSize from hlong,
    show ¬ (hash key).length > blockSize by omega, ite_true, ite_false]

/-- The MAC has the length of the hash output. -/
theorem lengthHmac {hash : List Nat → List Nat} {n : Nat}
    (hlen : ∀ m, (hash m).length = n) (blockSize : Nat) (key msg : List Nat) :
    (hmac hash blockSize key msg).length = n :=
  hlen _

/-- HMAC-SHA-256 gives 32 bytes. -/
theorem lengthSha256 (key msg : List Nat) : (sha256 key msg).length = Sha256.digestSize :=
  lengthHmac Sha256.lengthDigest _ key msg

/-- HMAC-SHA-512 gives 64 bytes. -/
theorem lengthSha512 (key msg : List Nat) : (sha512 key msg).length = Sha512.digestSize :=
  lengthHmac Sha512.lengthDigest _ key msg

/-- HMAC-SHA-256 is the RFC 2104 formula with the literal pads and the
64-byte block. -/
example (key msg : List Nat) :
    sha256 key msg =
      Sha256.digest ((normKey Sha256.digest 64 key).map (· ^^^ 0x5c) ++
        Sha256.digest ((normKey Sha256.digest 64 key).map (· ^^^ 0x36) ++ msg)) :=
  rfl

/-- A SHA-256 key always normalizes to one 64-byte block. -/
example (key : List Nat) : (normKey Sha256.digest Sha256.blockSize key).length = 64 :=
  lengthNormKey (fun m => by rw [Sha256.lengthDigest]; decide) key

/-- A long SHA-256 key can be hashed before calling HMAC. -/
example {key : List Nat} (hlong : 64 < key.length) (msg : List Nat) :
    sha256 key msg = sha256 (Sha256.digest key) msg :=
  hmacLongKey (fun m => by rw [Sha256.lengthDigest]; decide) hlong msg

end CryptoPure.Hmac
