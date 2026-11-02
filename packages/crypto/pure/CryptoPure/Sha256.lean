import CryptoPure.Constants
import CryptoPure.Preprocess
import CryptoPure.Mock.Bytes

/-!
# SHA-256

FIPS 180-4 §6.2 over the `List Nat` model, with a `ByteArray` form for
the IO edge. This is the audited copy and the oracle for the W3.3
cross-check (ARCHITECTURE §4.6). Production SHA-256 routes to
`LeanHazmatSha256` through the `Crypto` facade. This copy makes no
constant-time claim.

The hash state is a `Vector UInt32 8`: eight words, with the count in
the type. `UInt32` addition wraps mod 2³², the addition FIPS 180-4
§3.2 specifies, so the code needs no masks.
-/

set_option autoImplicit false

namespace CryptoPure.Sha256

open Preprocess

/-- ROTR, rotate right (FIPS 180-4 §3.2). `UInt32` shifts take the
amount mod 32. -/
def rotr (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Ch (FIPS 180-4 §4.1.2). -/
def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- Maj (FIPS 180-4 §4.1.2). -/
def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ₀ (FIPS 180-4 §4.1.2; BSIG0 in RFC 6234). -/
def bsig0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ₁ (FIPS 180-4 §4.1.2; BSIG1 in RFC 6234). -/
def bsig1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ₀ (FIPS 180-4 §4.1.2; SSIG0 in RFC 6234). -/
def ssig0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- σ₁ (FIPS 180-4 §4.1.2; SSIG1 in RFC 6234). -/
def ssig1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The message schedule W₀ … W₆₃ of one block (FIPS 180-4 §6.2.2,
step 1). The first 16 words are the block itself, and each later word
mixes four earlier ones. `getD` reads stay inside the array: entry `t`
reads only entries below `t`. -/
def schedule (block : List Nat) : Array UInt32 :=
  let w := words32 block
  (List.range 48).foldl (fun w i =>
    let t := i + 16
    w.push (ssig1 (w.getD (t - 2) 0) + w.getD (t - 7) 0 +
      ssig0 (w.getD (t - 15) 0) + w.getD (t - 16) 0)) w

/-- The compression of one 64-byte block into the hash state (FIPS
180-4 §6.2.2, steps 2 to 4): 64 rounds over the working variables
`a … h`, then the sum with the incoming state. -/
def compress (h : Vector UInt32 8) (block : List Nat) : Vector UInt32 8 :=
  let w := schedule block
  -- `Fin.foldl n f v` applies `f` for `t = 0, 1, …, n - 1` in order,
  -- threading the working variables through the rounds.
  let v := Fin.foldl 64 (fun (v : Vector UInt32 8) t =>
    let t1 := v[7] + bsig1 v[4] + ch v[4] v[5] v[6] + K[t] + w.getD t 0
    let t2 := bsig0 v[0] + maj v[0] v[1] v[2]
    #v[t1 + t2, v[0], v[1], v[2], v[3] + t1, v[4], v[5], v[6]]) h
  Vector.zipWith (· + ·) h v

/-- The SHA-256 digest of a message, 32 bytes. This copy makes no
constant-time claim (ARCHITECTURE §4.6). -/
def digest (msg : List Nat) : List Nat :=
  let h := (blocks blockSize (pad blockSize lengthBytes msg)).foldl compress H0
  h.toList.flatMap word32Bytes

/-- The digest over `ByteArray`, using the model digest and the byte
conversions (`digestBEq`). -/
def digestB (msg : ByteArray) : ByteArray :=
  Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg))

/-- Converting to model bytes, hashing, and converting back gives
`digestB`. -/
theorem digestBEq (msg : ByteArray) :
    digestB msg = Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg)) :=
  rfl

/-- Every digest is 32 bytes. -/
theorem lengthDigest (msg : List Nat) : (digest msg).length = digestSize := by
  simp [digest, List.length_flatMap, lengthWord32Bytes, List.map_const',
    digestSize]

/-- Every digest entry fits in a byte. -/
theorem ltOfMemDigest (msg : List Nat) : ∀ b ∈ digest msg, b < 256 := by
  intro b hb
  simp only [digest, List.mem_flatMap] at hb
  obtain ⟨w, _, hw⟩ := hb
  exact ltOfMemBeBytes 4 w.toNat b hw

/-- Converting a digest entry to `UInt8` preserves its value. -/
example (msg : List Nat) (b : Nat) (hb : b ∈ digest msg) :
    (UInt8.ofNat b).toNat = b := by
  simp [Nat.mod_eq_of_lt (ltOfMemDigest msg b hb)]

end CryptoPure.Sha256
