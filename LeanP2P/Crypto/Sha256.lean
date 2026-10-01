import LeanP2P.Crypto.Bytes
/-!
# SHA-256

Straightforward pure implementation over the `List Nat` byte model
(correctness anchored by NIST/spec vectors in the test suite, including the
multihash spec vector sha2-256("multihash")).
-/

namespace LeanP2P.Sha256

def K : List UInt32 :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : List UInt32 :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def be32 (bs : List Nat) : UInt32 :=
  ((bs.getD 0 0) * 16777216 + (bs.getD 1 0) * 65536 + (bs.getD 2 0) * 256 + (bs.getD 3 0)).toUInt32

def words (chunk : List Nat) : Array UInt32 :=
  let w0 := (List.range 16).foldl (fun a i => a.push (be32 (chunk.drop (4 * i)))) #[]
  (List.range 48).foldl (fun a i =>
    let wAt (j : Nat) : UInt32 := a.getD j 0
    let s0 (x : UInt32) : UInt32 := (rotr x 7) ^^^ (rotr x 18) ^^^ (x >>> 3)
    let s1 (x : UInt32) : UInt32 := (rotr x 17) ^^^ (rotr x 19) ^^^ (x >>> 10)
    let j := 16 + i
    a.push (wAt (j - 16) + s0 (wAt (j - 15)) + wAt (j - 7) + s1 (wAt (j - 2)))) w0

def compress (state : Array UInt32) (chunk : List Nat) : Array UInt32 :=
  let w := words chunk
  let out := (List.range 64).foldl (fun st i =>
    let a := st.getD 0 0; let b := st.getD 1 0; let c := st.getD 2 0; let d := st.getD 3 0
    let e := st.getD 4 0; let f := st.getD 5 0; let g := st.getD 6 0; let hh := st.getD 7 0
    let S1 := (rotr e 6) ^^^ (rotr e 11) ^^^ (rotr e 25)
    let ch := (e &&& f) ^^^ ((e ^^^ 0xFFFFFFFF) &&& g)
    let t1 := hh + S1 + ch + (K.getD i 0) + (w.getD i 0)
    let S0 := (rotr a 2) ^^^ (rotr a 13) ^^^ (rotr a 22)
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    #[t1 + t2, a, b, c, d + t1, e, f, g]) state
  -- chaining value: incoming state + working vars (found by the multi-block
  -- NIST vector; single-block digests masked this)
  (state.zip out).map (fun p => p.1 + p.2)

partial def run (state : Array UInt32) (bs : List Nat) : Array UInt32 :=
  if bs.isEmpty then state
  else run (compress state (bs.take 64)) (bs.drop 64)

def pad (msg : List Nat) : List Nat :=
  let l := msg.length
  let bits := l * 8
  -- zero-run k solves l + 1 + k + 8 = 0 (mod 64). Written subtraction-safe
  -- for Nat (no truncated subtraction): 119 = 55 + 64.
  msg ++ [128] ++ List.replicate ((119 - l % 64) % 64) 0 ++
    [bits / 72057594037927936 % 256, bits / 281474976710656 % 256,
     bits / 1099511627776 % 256, bits / 4294967296 % 256,
     bits / 16777216 % 256, bits / 65536 % 256, bits / 256 % 256, bits % 256]

def wordBytes (w : UInt32) : List Nat :=
  [(w >>> 24).toUInt8.toNat, (w >>> 16).toUInt8.toNat, (w >>> 8).toUInt8.toNat, w.toUInt8.toNat]

/-- SHA-256 digest as 32 bytes (`List Nat` model). -/
def digest (msg : List Nat) : List Nat :=
  -- `compress` folds the chaining value in, so the final state is the digest
  (run H0.toArray (pad msg)).toList.flatMap wordBytes

/-! ## ByteArray entry point (phase 2 step 14)

Same digest over the IO byte model; `Tests/Hashes` checks the two agree on
every run, so the production path cannot drift from the proof view. -/

/-- SHA-256 digest as 32 bytes over `ByteArray`. -/
def digestB (msg : ByteArray) : ByteArray :=
  Bytes.ofNatList (digest (Bytes.toNatList msg))

end LeanP2P.Sha256
