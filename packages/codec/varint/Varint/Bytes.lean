import Varint.UVarint

/-!
# The varint on `ByteArray`

The production path: the wire runs on bytes, so the decoder reads a
`ByteArray` in place. It returns the number of bytes it consumed, so a
framing layer knows where its payload starts. The generic harness of
`base/bytes` pins this decoder to the model core, `decode?`, on every
run (ARCHITECTURE §6, layer 3); the model carries the theorems.
-/

set_option autoImplicit false

namespace Varint

open Bytes

/-- The wire bytes of a varint. -/
def encodeB (v : UVarint) : ByteArray :=
  ofNatList (encode v)

/-- One varint from the front of `b`, and the number of bytes it took.
The rules are the rules of `decode?`: a zero terminator after a
continuation is `malformed`, a ninth byte that continues is
`malformed`, and an input that ends inside a varint is `truncated`. -/
def decodeB? (b : ByteArray) : Except DecodeError (UVarint × Nat) :=
  go 0 0
where
  /-- Byte `i` on, with `acc` the value of the groups before it. The
  index climbs toward the budget, so `maxBytes - i` decreases. -/
  go (i acc : Nat) : Except DecodeError (UVarint × Nat) :=
    if h : i < b.size then
      let byte := b[i].toNat
      if byte < 128 then
        if byte = 0 ∧ 0 < i then .error .malformed
        else
          let v := acc + byte * 128 ^ i
          if hv : v < limit then .ok (⟨v, hv⟩, i + 1) else .error .malformed
      else if i + 1 < maxBytes then go (i + 1) (acc + (byte - 128) * 128 ^ i)
      else .error .malformed
    else .error .truncated
  termination_by maxBytes - i

/-- One varint at byte `pos` of `b`, and the position after it.

A protobuf field, a multihash, or a frame header holds its varints
inside a larger buffer. `decodeB?` reads from the front of its input,
so a caller at an offset would have to cut the input first. A cut of
the whole tail copies the rest of the message for each varint. A
varint never takes more than `maxBytes` bytes, so this reader cuts a
window of `maxBytes` bytes at most. The window answers as the whole
tail would, and the copy stays at 9 bytes for any buffer size.

The errors are the errors of `decodeB?`. A `pos` at or past the end
of `b` gives an empty window, which is `truncated`. -/
def decodeAt? (b : ByteArray) (pos : Nat) : Except DecodeError (UVarint × Nat) :=
  let window := b.extract pos (min b.size (pos + maxBytes))
  (decodeB? window).map fun (v, used) => (v, pos + used)

-- `decodeAt?` reads at the offset and answers the position after the
-- varint, here 300 = `0xAC 0x02` at offset 1, so the next byte is at 3.
#guard match decodeAt? (Bytes.ofNatList [0xFF, 0xAC, 0x02, 0x07]) 1 with
  | .ok (v, next) => v.val == 300 && next == 3
  | .error _ => false

end Varint
