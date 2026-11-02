import CryptoPure.Constants
import CryptoPure.Preprocess
import CryptoPure.Mock.Bytes

/-!
# SHA-1

FIPS 180-4 §6.1 over the `List Nat` model, with a `ByteArray` form for
the IO edge. SHA-1 is here for the multihash function table, code
0x11: a peer may send a sha1 multihash, and the caller composes this
digest with the framing of `codec/multiformats` through the facade.
SHA-1 serves nothing security-relevant. This copy makes no
constant-time claim. It shares the padding and the block split of
SHA-256 (`Preprocess`), and it keeps a five-word state.
-/

set_option autoImplicit false

namespace CryptoPure.Sha1

open Preprocess

/-- ROTL, rotate left (FIPS 180-4 §3.2). -/
def rotl (x n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- fₜ (FIPS 180-4 §4.1.1): Ch for rounds 0 to 19, Parity for 20 to 39,
Maj for 40 to 59, and Parity again for 60 to 79. -/
def f (t : Nat) (x y z : UInt32) : UInt32 :=
  if t < 20 then (x &&& y) ^^^ (~~~x &&& z)
  else if t < 40 then x ^^^ y ^^^ z
  else if t < 60 then (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  else x ^^^ y ^^^ z

/-- The message schedule W₀ … W₇₉ of one block (FIPS 180-4 §6.1.2,
step 1). Entry `t` reads only entries below `t`. -/
def schedule (block : List Nat) : Array UInt32 :=
  let w := ((List.range 16).map fun t => be32 (block.drop (4 * t))).toArray
  (List.range 64).foldl (fun w i =>
    let t := i + 16
    w.push (rotl (w.getD (t - 3) 0 ^^^ w.getD (t - 8) 0 ^^^
      w.getD (t - 14) 0 ^^^ w.getD (t - 16) 0) 1)) w

/-- The compression of one 64-byte block into the hash state (FIPS
180-4 §6.1.2, steps 2 to 4). Round `t` takes the constant of its
20-round stage, `K[t / 20]`. -/
def compress (h : Vector UInt32 5) (block : List Nat) : Vector UInt32 5 :=
  let w := schedule block
  -- `Fin.foldl n f v` applies `f` for `t = 0, 1, …, n - 1` in order,
  -- threading the working variables through the rounds.
  let v := Fin.foldl 80 (fun (v : Vector UInt32 5) t =>
    let k := K[t.val / 20]'(by have := t.isLt; omega)
    let tmp := rotl v[0] 5 + f t v[1] v[2] v[3] + v[4] + k + w.getD t 0
    #v[tmp, v[0], rotl v[1] 30, v[2], v[3]]) h
  Vector.zipWith (· + ·) h v

/-- The SHA-1 digest of a message, 20 bytes. This copy makes no
constant-time claim (ARCHITECTURE §4.6). -/
def digest (msg : List Nat) : List Nat :=
  let h := (blocks blockSize (pad blockSize lengthBytes msg)).foldl compress H0
  h.toList.flatMap word32Bytes

/-- The digest over `ByteArray`, for the IO edge (`digestBEq`). -/
def digestB (msg : ByteArray) : ByteArray :=
  Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg))

theorem digestBEq (msg : ByteArray) :
    digestB msg = Mock.Bytes.ofNatList (digest (Mock.Bytes.toNatList msg)) :=
  rfl

/-- Every digest is 20 bytes. -/
theorem lengthDigest (msg : List Nat) : (digest msg).length = digestSize := by
  simp [digest, List.length_flatMap, lengthWord32Bytes, List.map_const', digestSize]

/-- Every block the compression reads is a full 64 bytes. -/
theorem lengthOfMemBlocks (msg : List Nat) :
    ∀ b ∈ blocks blockSize (pad blockSize lengthBytes msg), b.length = blockSize :=
  lengthOfMemBlocksPad (by decide) lengthBytes msg

-- FIPS 180-4 example: SHA-1("abc"). The build evaluates this.
#guard digest [0x61, 0x62, 0x63] ==
  [0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, 0xba, 0x3e,
   0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c, 0x9c, 0xd0, 0xd8, 0x9d]

end CryptoPure.Sha1
