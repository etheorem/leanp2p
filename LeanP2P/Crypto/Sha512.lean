import LeanP2P.Crypto.Bytes
/-!
# SHA-512

Same shape as `Crypto/Sha256`: pure implementation over the `List Nat` byte
model over `UInt64` words (FIPS 180-4). Needed by Ed25519 (RFC 8032) and by
the Noise handshake's HKDF choice; correctness is anchored by the RFC
4634-style vectors in `Tests/Hashes` and cross-checked against OpenSSL at
the IO edge.
-/

namespace LeanP2P.Sha512

def K : List UInt64 :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def H0 : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

def be64 (bs : List Nat) : UInt64 :=
  ((bs.getD 0 0) * 72057594037927936 + (bs.getD 1 0) * 281474976710656 +
   (bs.getD 2 0) * 1099511627776 + (bs.getD 3 0) * 4294967296 +
   (bs.getD 4 0) * 16777216 + (bs.getD 5 0) * 65536 + (bs.getD 6 0) * 256 +
   (bs.getD 7 0)).toUInt64

def words (chunk : List Nat) : Array UInt64 :=
  let w0 := (List.range 16).foldl (fun a i => a.push (be64 (chunk.drop (8 * i)))) #[]
  (List.range 64).foldl (fun a i =>
    let wAt (j : Nat) : UInt64 := a.getD j 0
    let s0 (x : UInt64) : UInt64 := (rotr x 1) ^^^ (rotr x 8) ^^^ (x >>> 7)
    let s1 (x : UInt64) : UInt64 := (rotr x 19) ^^^ (rotr x 61) ^^^ (x >>> 6)
    let j := 16 + i
    a.push (wAt (j - 16) + s0 (wAt (j - 15)) + wAt (j - 7) + s1 (wAt (j - 2)))) w0

def compress (state : Array UInt64) (chunk : List Nat) : Array UInt64 :=
  let w := words chunk
  let out := (List.range 80).foldl (fun st i =>
    let a := st.getD 0 0; let b := st.getD 1 0; let c := st.getD 2 0; let d := st.getD 3 0
    let e := st.getD 4 0; let f := st.getD 5 0; let g := st.getD 6 0; let hh := st.getD 7 0
    let S1 := (rotr e 14) ^^^ (rotr e 18) ^^^ (rotr e 41)
    let ch := (e &&& f) ^^^ ((e ^^^ 0xFFFFFFFFFFFFFFFF) &&& g)
    let t1 := hh + S1 + ch + (K.getD i 0) + (w.getD i 0)
    let S0 := (rotr a 28) ^^^ (rotr a 34) ^^^ (rotr a 39)
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    #[t1 + t2, a, b, c, d + t1, e, f, g]) state
  -- chaining value: incoming state + working vars (as in Sha256.compress)
  (state.zip out).map (fun p => p.1 + p.2)

partial def run (state : Array UInt64) (bs : List Nat) : Array UInt64 :=
  if bs.isEmpty then state
  else run (compress state (bs.take 128)) (bs.drop 128)

def pad (msg : List Nat) : List Nat :=
  let l := msg.length
  let bits := l * 8
  -- zero-run k solves l + 1 + k + 16 = 0 (mod 128): k = (111 - l) mod 128,
  -- written subtraction-safe for Nat (239 = 111 + 128)
  msg ++ [128] ++ List.replicate ((239 - l % 128) % 128) 0 ++
    (List.range 16).map (fun i => bits / (2 ^ (8 * (15 - i))) % 256)

def wordBytes (w : UInt64) : List Nat :=
  [(w >>> 56).toUInt8.toNat, (w >>> 48).toUInt8.toNat, (w >>> 40).toUInt8.toNat,
   (w >>> 32).toUInt8.toNat, (w >>> 24).toUInt8.toNat, (w >>> 16).toUInt8.toNat,
   (w >>> 8).toUInt8.toNat, w.toUInt8.toNat]

/-- SHA-512 digest as 64 bytes (`List Nat` model). -/
def digest (msg : List Nat) : List Nat :=
  (run H0 (pad msg)).toList.flatMap wordBytes

end LeanP2P.Sha512
