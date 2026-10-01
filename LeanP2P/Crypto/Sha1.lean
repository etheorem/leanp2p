/-!
# SHA-1

Pure reference implementation over the `List Nat` byte model. Only needed
for the multihash README's sha1 example vector (multihash code 0x11); it
must not be used for anything security-relevant.
-/

namespace LeanP2P.Sha1

private def two32 : Nat := 0x100000000

private def rotl (n x : Nat) : Nat :=
  ((x <<< n) + (x >>> (32 - n))) % two32

private def word (x : Nat) : List Nat :=
  [x / 0x1000000 % 256, x / 0x10000 % 256, x / 256 % 256, x % 256]

private def mask32 (x : Nat) : Nat := x % two32

/-- SHA-1 digest of a byte string (`List Nat` model). -/
def digest (bs : List Nat) : List Nat :=
  -- padding: message, 0x80, zeros to 56 mod 64, 64-bit big-endian bit length
  let bitLen := bs.length * 8
  let padded :=
    bs ++ [0x80] ++ List.replicate ((119 - bs.length % 64) % 64) 0 ++
    [0, 0, 0, 0, bitLen / 0x1000000 % 256,
      bitLen / 0x10000 % 256, bitLen / 256 % 256, bitLen % 256]
  let blocks : List (List Nat) :=
    (List.range (padded.length / 64)).map
      (fun i => ((padded.drop (i * 64)).take 64))
  let final :=
    blocks.foldl step (0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0)
  let (a, b, c, d, e) := final
  word a ++ word b ++ word c ++ word d ++ word e
where
  step (st : Nat × Nat × Nat × Nat × Nat) (block : List Nat) :
      Nat × Nat × Nat × Nat × Nat :=
    let (a0, b0, c0, d0, e0) := st
    let w : Nat → Nat := fun i =>
      let j := i * 4
      0x1000000 * (block.getD j 0) + 0x10000 * (block.getD (j + 1) 0) +
        256 * (block.getD (j + 2) 0) + (block.getD (j + 3) 0)
    -- message schedule: extend to 80 words
    let ws : List Nat :=
      Id.run do
        let mut ws := (List.range 16).map w
        for i in [16:80] do
          let x := ws.getD (i - 3) 0 ^^^ ws.getD (i - 8) 0 ^^^
                   ws.getD (i - 14) 0 ^^^ ws.getD (i - 16) 0
          ws := ws ++ [rotl 1 x]
        ws
    let rounds := (List.range 80).foldl (fun st i =>
      let (a, b, c, d, e) := st
      let f := if i < 20 then (b &&& c) ||| (mask32 (0xFFFFFFFF - b) &&& d)
               else if i < 40 then b ^^^ c ^^^ d
               else if i < 60 then (b &&& c) ||| (b &&& d) ||| (c &&& d)
               else b ^^^ c ^^^ d
      let kk := if i < 20 then 0x5A827999
                else if i < 40 then 0x6ED9EBA1
                else if i < 60 then 0x8F1BBCDC
                else 0xCA62C1D6
      let tmp := mask32 (rotl 5 a + f + e + kk + ws.getD i 0)
      (tmp, a, rotl 30 b, c, d)) st
    let (a, b, c, d, e) := rounds
    (mask32 (a + a0), mask32 (b + b0), mask32 (c + c0), mask32 (d + d0),
      mask32 (e + e0))

end LeanP2P.Sha1
