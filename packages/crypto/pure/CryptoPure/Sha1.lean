import CryptoPure.Constants
import CryptoPure.Preprocess
import Bytes

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
  let w := words32 block
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

/-- The digest over `ByteArray`, using the model digest and the byte
conversions (`digestBEq`). -/
def digestB (msg : ByteArray) : ByteArray :=
  Bytes.ofNatList (digest (Bytes.toNatList msg))

/-- Converting to model bytes, hashing, and converting back gives
`digestB`. -/
theorem digestBEq (msg : ByteArray) :
    digestB msg = Bytes.ofNatList (digest (Bytes.toNatList msg)) :=
  rfl

/-- Every digest is 20 bytes. -/
theorem lengthDigest (msg : List Nat) : (digest msg).length = digestSize := by
  simp [digest, List.length_flatMap, lengthWord32Bytes, List.map_const', digestSize]

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

end CryptoPure.Sha1
