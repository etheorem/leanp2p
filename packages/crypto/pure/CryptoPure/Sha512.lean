import CryptoPure.Constants
import CryptoPure.Preprocess
import CryptoPure.Mock.Bytes

/-!
# SHA-512

FIPS 180-4 §6.4 over the `List Nat` model, with a `ByteArray` form for
the IO edge. The shape is SHA-256's, over 64-bit words, 128-byte
blocks, and 80 rounds. This is the audited copy, and the oracle of the
W3.3 cross-check (ARCHITECTURE §4.6). Production SHA-512 is the
backend binding behind the `Crypto` facade. This copy makes no
constant-time claim.
-/

set_option autoImplicit false

namespace CryptoPure.Sha512

open Preprocess

/-- ROTR, rotate right (FIPS 180-4 §3.2). `UInt64` shifts take the
amount mod 64. -/
def rotr (x n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- Ch (FIPS 180-4 §4.1.3). -/
def ch (x y z : UInt64) : UInt64 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- Maj (FIPS 180-4 §4.1.3). -/
def maj (x y z : UInt64) : UInt64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ₀ (FIPS 180-4 §4.1.3; BSIG0 in RFC 6234). -/
def bsig0 (x : UInt64) : UInt64 :=
  rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39

/-- Σ₁ (FIPS 180-4 §4.1.3; BSIG1 in RFC 6234). -/
def bsig1 (x : UInt64) : UInt64 :=
  rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41

/-- σ₀ (FIPS 180-4 §4.1.3; SSIG0 in RFC 6234). -/
def ssig0 (x : UInt64) : UInt64 :=
  rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)

/-- σ₁ (FIPS 180-4 §4.1.3; SSIG1 in RFC 6234). -/
def ssig1 (x : UInt64) : UInt64 :=
  rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)

/-- The message schedule W₀ … W₇₉ of one block (FIPS 180-4 §6.4.2,
step 1). Entry `t` reads only entries below `t`. -/
def schedule (block : List Nat) : Array UInt64 :=
  let w := ((List.range 16).map fun t => be64 (block.drop (8 * t))).toArray
  (List.range 64).foldl (fun w i =>
    let t := i + 16
    w.push (ssig1 (w.getD (t - 2) 0) + w.getD (t - 7) 0 +
      ssig0 (w.getD (t - 15) 0) + w.getD (t - 16) 0)) w

/-- The compression of one 128-byte block into the hash state (FIPS
180-4 §6.4.2, steps 2 to 4). -/
def compress (h : Vector UInt64 8) (block : List Nat) : Vector UInt64 8 :=
  let w := schedule block
  -- `Fin.foldl n f v` applies `f` for `t = 0, 1, …, n - 1` in order,
  -- threading the working variables through the rounds.
  let v := Fin.foldl 80 (fun (v : Vector UInt64 8) t =>
    let t1 := v[7] + bsig1 v[4] + ch v[4] v[5] v[6] + K[t] + w.getD t 0
    let t2 := bsig0 v[0] + maj v[0] v[1] v[2]
    #v[t1 + t2, v[0], v[1], v[2], v[3] + t1, v[4], v[5], v[6]]) h
  Vector.zipWith (· + ·) h v

/-- The SHA-512 digest of a message, 64 bytes. This copy makes no
constant-time claim (ARCHITECTURE §4.6). -/
def digest (msg : List Nat) : List Nat :=
  let h := (blocks blockSize (pad blockSize lengthBytes msg)).foldl compress H0
  h.toList.flatMap word64Bytes

/-- The digest over `ByteArray`, for the IO edge (`digestBEq`). -/
def digestB (msg : ByteArray) : ByteArray :=
  Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg))

theorem digestBEq (msg : ByteArray) :
    digestB msg = Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg)) :=
  rfl

/-- Every digest is 64 bytes. -/
theorem lengthDigest (msg : List Nat) : (digest msg).length = digestSize := by
  simp [digest, List.length_flatMap, lengthWord64Bytes, List.map_const', digestSize]

/-- Every block the compression reads is a full 128 bytes. -/
theorem lengthOfMemBlocks (msg : List Nat) :
    ∀ b ∈ blocks blockSize (pad blockSize lengthBytes msg), b.length = blockSize :=
  lengthOfMemBlocksPad (by decide) lengthBytes msg

-- FIPS 180-4 example: SHA-512("abc"). The build evaluates this.
#guard digest [0x61, 0x62, 0x63] ==
  [0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
   0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
   0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
   0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f]

end CryptoPure.Sha512
