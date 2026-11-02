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

open Varint.Mock.Bytes

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

end Varint
