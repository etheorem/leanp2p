import Libp2p.Protocols.Constants

/-!
# CRC-32C and the snappy checksum mask

A snappy data chunk opens with the masked CRC-32C of its uncompressed
bytes (`vendor/snappy/framing_format.txt`, section 3). CRC-32C is the
Castagnoli CRC of RFC 3720, section 12.1: the reflected polynomial
`0x82f63b78`, the register starts at all ones, and the result is the
register with all bits flipped.

The module has two paths, as every codec of the tree has (CLAUDE.md,
"Proofs and tests"):

* `crc32c` is the model over the `List Nat` byte model. It shifts one
  bit at a time, so the definition reads as the RFC does.
* `crc32cB` runs on `ByteArray` with a 256-entry table, one lookup per
  byte. The suite pins it to the model, and it checks both against the
  examples of RFC 3720, appendix B.4.

`mask` is the rotate-and-add of section 3. The reader compares the mask
of its own checksum with the stored value, so no unmask is needed.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp.Crc32c

open Libp2p.Protocols

/-- The reflected Castagnoli polynomial, RFC 3720 section 12.1. -/
def poly : Nat := 0x82f63b78

/-- The register value before the first byte, and the final flip. -/
def allOnes : Nat := 0xffffffff

/-! ## The model -/

/-- Shift the register `k` times, one bit each time. When the low bit
falls out set, the polynomial is added (XOR). -/
def shiftBits : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => shiftBits k (if c % 2 = 1 then (c / 2) ^^^ poly else c / 2)

/-- Feed one byte into the register. -/
def feed (c b : Nat) : Nat := shiftBits 8 (c ^^^ b)

/-- The CRC-32C of a byte list. -/
def crc32c (bs : List Nat) : Nat := bs.foldl feed allOnes ^^^ allOnes

/-- The checksum mask of the snappy framing format: rotate right by 15
bits, then add `0xa282ead8`, both modulo 2^32. -/
def mask (x : Nat) : Nat :=
  ((x / 2 ^ 15 ||| x * 2 ^ 17 % 2 ^ 32) + Constants.snappyMaskDelta) % 2 ^ 32

/-- The checksum of an empty input is zero, since the flip undoes the
start value. -/
theorem crc32cNil : crc32c [] = 0 := by decide

/-! ## The `ByteArray` path -/

/-- One table entry: the register after eight shifts from the byte `i`. -/
def entry (i : Nat) : UInt32 := (shiftBits 8 i).toUInt32

/-- The 256 entries, one per byte value. -/
def table : Array UInt32 := (Array.range 256).map entry

/-- The table holds one entry per byte value. -/
theorem tableSize : table.size = 256 := by simp [table]

/-- The CRC-32C of a `ByteArray`, one table lookup per byte. -/
def crc32cB (b : ByteArray) : UInt32 :=
  let step (c : UInt32) (x : UInt8) : UInt32 :=
    -- The index is below 256 by the mask, and `tableSize` says the table
    -- holds 256 entries, so `!` never takes its default.
    (c >>> 8) ^^^ table[((c ^^^ x.toUInt32) &&& 0xff).toNat]!
  b.foldl step 0xffffffff ^^^ 0xffffffff

/-- `mask` on `UInt32`. The shifts drop the bits that leave the word,
and the addition wraps. -/
def maskB (x : UInt32) : UInt32 :=
  ((x >>> 15) ||| (x <<< 17)) + Constants.snappyMaskDelta.toUInt32

end Libp2p.Protocols.ReqResp.Crc32c
