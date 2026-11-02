import Proto.Core

/-!
# ByteArray entry points

The encoder converts the proved model's output. The decoder walks the
ByteArray by position, with separate fixed-width and payload reads. Its
tests compare that path against the pure model, including error kinds
and consumed counts. Only varint decoding crosses the W2.1 mock seam.
-/

set_option autoImplicit false

namespace Pb

/-- The model encoder supplies exactly the wire bytes in field order. -/
def encodeFieldsB (fs : Fields) : ByteArray := Mock.Bytes.ofNatList (encodeFields fs)

/-- A budget-sized window avoids copying the remaining message for each varint. -/
private def readVarintAt (bs : ByteArray) (pos : Nat) :
    Except Error (Mock.Varint.UVarint × Nat) := do
  let window := bs.extract pos (min bs.size (pos + Mock.Varint.maxBytes))
  let (v, used) ← (Mock.Varint.decodeB? window).mapError Error.framing
  .ok (v, pos + used)

/-- Check the length before extracting a fixed-width or variable payload. -/
private def takeBytesAt (bs : ByteArray) (pos count : Nat) :
    Except Error (List Nat × Nat) :=
  if pos + count > bs.size then .error (.framing .truncated)
  else .ok ((bs.extract pos (pos + count)).toList.map UInt8.toNat, pos + count)

/-- Parse a value without converting the remaining message to the model. -/
private def decodeValueAt (wire : Nat) (bs : ByteArray) (pos : Nat) :
    Except Error (Value × Nat) := do
  match wire with
  | 0 =>
      let (v, next) ← readVarintAt bs pos
      .ok (.varint v.val, next)
  | 1 =>
      let (bytes, next) ← takeBytesAt bs pos 8
      .ok (.fixed64 (leOf bytes), next)
  | 2 =>
      let (count, next) ← readVarintAt bs pos
      let (payload, after) ← takeBytesAt bs next count.val
      .ok (.bytes payload, after)
  | 5 =>
      let (bytes, next) ← takeBytesAt bs pos 4
      .ok (.fixed32 (leOf bytes), next)
  | _ => .error .badWireType

/-- Each successful step must advance the cursor, even with an empty payload. -/
private def decodeEntryAt (bs : ByteArray) (pos : Nat) : Except Error (Entry × Nat) := do
  let (tag, next) ← readVarintAt bs pos
  let num := tag.val / 8
  if ¬ (0 < num ∧ num < fieldNumberLimit) then .error .badField
  else
    let (value, after) ← decodeValueAt (tag.val % 8) bs next
    if after ≤ pos then .error (.framing .malformed)
    else .ok ((num, value), after)

/-- The input size bounds the number of nonempty field encodings. -/
private def decodeBytesLoop (bs : ByteArray) : Nat → Nat → List Entry → Except Error Fields
  | fuel, pos, rev =>
      if pos = bs.size then Fields.ofList? rev.reverse
      else match fuel with
      | 0 => .error (.framing .malformed)
      | fuel + 1 => do
          let (entry, next) ← decodeEntryAt bs pos
          decodeBytesLoop bs fuel next (entry :: rev)

/-- Standalone messages consume their externally framed buffer in full. -/
def decodeFieldsB? (bs : ByteArray) : Except Error (Fields × Nat) := do
  let fs ← decodeBytesLoop bs bs.size 0 []
  .ok (fs, bs.size)

end Pb
