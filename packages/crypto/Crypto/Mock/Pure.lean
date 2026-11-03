import Bytes

/-!
# The mock of the `crypto/pure` surface

Unit W3.1 (`crypto/pure`, etheorem/leanp2p#4) has not merged. RULES.md,
"Working ahead of the tree", tells a unit to build against a mock of
the frozen interface of a dependency that has not merged. The mock
lives in a `Mock` namespace inside the unit's package. It declares the
surface with `opaque` declarations, and it imports nothing from the
real package. The pure package ARCHITECTURE, "Public surface", freezes
the surface, and the W3.1 pull request (etheorem/leanp2p#29) names it.
The cross-check calls these names:

* `Sha256.digestB`, `Sha512.digestB`, `Sha1.digestB` over `ByteArray`
* `Hmac.sha256` over the `List Nat` model
* `Hkdf.extractSha256` and `Hkdf.expandSha256` over the model.
  `expandSha256` returns `none` past 255 blocks (RFC 5869 §2.3).

**Why the opaques have values.** The cross-check compares two
implementations on real inputs, so a mock that returns a default value
fails every check. Lean compiles an `opaque` from the value that
follows `:=`. The kernel still sees no definition, so no proof can
unfold one. The values below are FIPS 180-4, RFC 2104, and RFC 5869,
written over `ByteArray` for this mock alone.

**Integration.** When W3.1 merges, the suite imports `CryptoPure` in
place of this module and drops `open Crypto.Mock`. The names resolve
to the real package unchanged, and the integration deletes this
module.
-/

set_option autoImplicit false

namespace Crypto.Mock.CryptoPure

namespace Impl

/-! ## Padding and words (FIPS 180-4 §3, §5.1) -/

/-- `n` as `width` big-endian bytes, the excess high bits dropped. -/
def beBytes (width n : Nat) : ByteArray :=
  ByteArray.mk ((List.range width).reverse.map fun i => (n / 256 ^ i % 256).toUInt8).toArray

/-- The padded message: the message, `0x80`, zeros, and the bit length
in `lenBytes` big-endian bytes, to a multiple of `block` bytes. -/
def pad (block lenBytes : Nat) (m : ByteArray) : ByteArray :=
  let r := (m.size + 1 + lenBytes) % block
  let zeros := if r = 0 then 0 else block - r
  m.push 0x80 ++ ByteArray.mk (Array.replicate zeros 0) ++ beBytes lenBytes (8 * m.size)

/-- The big-endian word of `width` bytes at offset `i`. -/
def beWord (b : ByteArray) (i width : Nat) : Nat :=
  (List.range width).foldl (fun acc k => acc * 256 + (b.get! (i + k)).toNat) 0

/-- The digest bytes of a final state of `width`-byte words. -/
def output (width : Nat) (ws : List Nat) : ByteArray :=
  ws.foldl (fun acc w => acc ++ beBytes width w) .empty

/-! ## SHA-256 (FIPS 180-4 §6.2) -/

def k256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def h256 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
  0x1f83d9ab, 0x5be0cd19]

def rotr32 (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- One 64-byte block at offset `off` of the padded message `p`. -/
def compress256 (h : Array UInt32) (p : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    w := w.push (beWord p (off + 4 * t) 4).toUInt32
  for t in [16:64] do
    let s0 := rotr32 w[t-15]! 7 ^^^ rotr32 w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
    let s1 := rotr32 w[t-2]! 17 ^^^ rotr32 w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
    w := w.push (s1 + w[t-7]! + s0 + w[t-16]!)
  let mut v := h
  for t in [0:64] do
    let a := v[0]!
    let e := v[4]!
    let t1 := v[7]! + (rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25) +
      ((e &&& v[5]!) ^^^ (~~~e &&& v[6]!)) + k256[t]! + w[t]!
    let t2 := (rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22) +
      ((a &&& v[1]!) ^^^ (a &&& v[2]!) ^^^ (v[1]! &&& v[2]!))
    v := #[t1 + t2, a, v[1]!, v[2]!, v[3]! + t1, e, v[5]!, v[6]!]
  return (h.zip v).map fun p => p.1 + p.2

def sha256 (m : ByteArray) : ByteArray :=
  let p := pad 64 8 m
  let h := (List.range (p.size / 64)).foldl (fun h i => compress256 h p (64 * i)) h256
  output 4 (h.toList.map (·.toNat))

/-! ## SHA-512 (FIPS 180-4 §6.4) -/

def k512 : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
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

def h512 : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def rotr64 (x n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- One 128-byte block at offset `off` of the padded message `p`. -/
def compress512 (h : Array UInt64) (p : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := #[]
  for t in [0:16] do
    w := w.push (beWord p (off + 8 * t) 8).toUInt64
  for t in [16:80] do
    let s0 := rotr64 w[t-15]! 1 ^^^ rotr64 w[t-15]! 8 ^^^ (w[t-15]! >>> 7)
    let s1 := rotr64 w[t-2]! 19 ^^^ rotr64 w[t-2]! 61 ^^^ (w[t-2]! >>> 6)
    w := w.push (s1 + w[t-7]! + s0 + w[t-16]!)
  let mut v := h
  for t in [0:80] do
    let a := v[0]!
    let e := v[4]!
    let t1 := v[7]! + (rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41) +
      ((e &&& v[5]!) ^^^ (~~~e &&& v[6]!)) + k512[t]! + w[t]!
    let t2 := (rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39) +
      ((a &&& v[1]!) ^^^ (a &&& v[2]!) ^^^ (v[1]! &&& v[2]!))
    v := #[t1 + t2, a, v[1]!, v[2]!, v[3]! + t1, e, v[5]!, v[6]!]
  return (h.zip v).map fun p => p.1 + p.2

def sha512 (m : ByteArray) : ByteArray :=
  let p := pad 128 16 m
  let h := (List.range (p.size / 128)).foldl (fun h i => compress512 h p (128 * i)) h512
  output 8 (h.toList.map (·.toNat))

/-! ## SHA-1 (FIPS 180-4 §6.1) -/

def rotl32 (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- One 64-byte block at offset `off` of the padded message `p`. -/
def compress1 (h : Array UInt32) (p : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    w := w.push (beWord p (off + 4 * t) 4).toUInt32
  for t in [16:80] do
    w := w.push (rotl32 (w[t-3]! ^^^ w[t-8]! ^^^ w[t-14]! ^^^ w[t-16]!) 1)
  let mut v := h
  for t in [0:80] do
    let (b, c, d) := (v[1]!, v[2]!, v[3]!)
    -- f and K change every 20 rounds (FIPS 180-4 §4.1.1, §4.2.1).
    let (f, k) : UInt32 × UInt32 :=
      if t < 20 then ((b &&& c) ||| (~~~b &&& d), 0x5a827999)
      else if t < 40 then (b ^^^ c ^^^ d, 0x6ed9eba1)
      else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8f1bbcdc)
      else (b ^^^ c ^^^ d, 0xca62c1d6)
    let temp := rotl32 v[0]! 5 + f + v[4]! + k + w[t]!
    v := #[temp, v[0]!, rotl32 b 30, c, d]
  return (h.zip v).map fun p => p.1 + p.2

def sha1 (m : ByteArray) : ByteArray :=
  let p := pad 64 8 m
  let h := (List.range (p.size / 64)).foldl (fun h i => compress1 h p (64 * i))
    #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
  output 4 (h.toList.map (·.toNat))

/-! ## HMAC (RFC 2104) and HKDF (RFC 5869) over SHA-256 -/

/-- HMAC-SHA-256. HMAC hashes a key longer than the 64-byte block
first, then pads the key with zeros to the block. -/
def hmac256 (key msg : ByteArray) : ByteArray :=
  let k := if key.size > 64 then sha256 key else key
  let k := k ++ ByteArray.mk (Array.replicate (64 - k.size) 0)
  let inner := ByteArray.mk (k.data.map (· ^^^ 0x36))
  let outer := ByteArray.mk (k.data.map (· ^^^ 0x5c))
  sha256 (outer ++ sha256 (inner ++ msg))

/-- HKDF-Extract: an empty salt becomes 32 zero bytes (RFC 5869 §2.2). -/
def extract256 (salt ikm : ByteArray) : ByteArray :=
  hmac256 (if salt.size == 0 then ByteArray.mk (Array.replicate 32 0) else salt) ikm

/-- HKDF-Expand: `T(i) = HMAC(prk, T(i-1) ‖ info ‖ i)`, at most 255
blocks (RFC 5869 §2.3). -/
def expand256 (prk info : ByteArray) (len : Nat) : Option ByteArray := Id.run do
  if len > 255 * 32 then return none
  let mut okm := ByteArray.empty
  let mut t := ByteArray.empty
  for i in [1:(len + 31) / 32 + 1] do
    t := hmac256 prk ((t ++ info).push i.toUInt8)
    okm := okm ++ t
  return some (okm.extract 0 len)

end Impl

/-! ## The frozen surface -/

namespace Sha256
/-- SHA-256 over `ByteArray`, 32 bytes. -/
opaque digestB : ByteArray → ByteArray := Impl.sha256
end Sha256

namespace Sha512
/-- SHA-512 over `ByteArray`, 64 bytes. -/
opaque digestB : ByteArray → ByteArray := Impl.sha512
end Sha512

namespace Sha1
/-- SHA-1 over `ByteArray`, 20 bytes. -/
opaque digestB : ByteArray → ByteArray := Impl.sha1
end Sha1

namespace Hmac
/-- HMAC-SHA-256 over the model, 32 bytes. -/
opaque sha256 : List Nat → List Nat → List Nat := fun key msg =>
  Bytes.toNatList (Impl.hmac256 (Bytes.ofNatList key) (Bytes.ofNatList msg))
end Hmac

namespace Hkdf
/-- HKDF-SHA-256 extract over the model, 32 bytes. -/
opaque extractSha256 : List Nat → List Nat → List Nat := fun salt ikm =>
  Bytes.toNatList (Impl.extract256 (Bytes.ofNatList salt) (Bytes.ofNatList ikm))

/-- HKDF-SHA-256 expand over the model, or `none` past 255 blocks. -/
opaque expandSha256 : List Nat → List Nat → Nat → Option (List Nat) := fun prk info len =>
  (Impl.expand256 (Bytes.ofNatList prk) (Bytes.ofNatList info) len).map Bytes.toNatList
end Hkdf

end Crypto.Mock.CryptoPure
