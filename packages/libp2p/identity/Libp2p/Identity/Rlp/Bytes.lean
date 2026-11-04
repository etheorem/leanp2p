import Libp2p.Identity.Rlp

/-!
# RLP on `ByteArray`

The production path: the wire runs on bytes, so the decoder walks a
`ByteArray` by position, and `lim` marks the end of the enclosing
payload. It mirrors the model of `Rlp.lean` step for step, so the
errors agree as well as the values. The generic harness of
`base/bytes` pins it to the model core, `decode?`, in `Tests/Rlp.lean`
(ARCHITECTURE §6, layer 3); the model carries the theorems.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Rlp

open Bytes

namespace Wire

/-- The byte at `i`, as a model value. Callers check `i < lim ≤ size`. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

/-- The bytes `[i, j)` as the model list. -/
def slice (b : ByteArray) (i j : Nat) : List Nat := toNatList (b.extract i j)

end Wire

open Wire in
/-- The long-form length: `k` bytes at `pos`, before `lim`. -/
def longLengthB (b : ByteArray) (k pos lim : Nat) : Except DecodeError (Nat × Nat) :=
  if lim - pos < k then .error .truncated
  else
    let lb := slice b pos (pos + k)
    if lb.head? = some 0 then .error .malformed
    else if beNat lb < 56 then .error .malformed
    else .ok (beNat lb, pos + k)

open Wire in
/-- The header at `pos`, before `lim`, and the position after it. -/
def decodeHeadB (b : ByteArray) (pos lim : Nat) : Except DecodeError (Head × Nat) :=
  if lim ≤ pos then .error .truncated
  else
    let c := byteAt b pos
    if c < 0x80 then .ok (.single c, pos + 1)
    else if c < 0xb8 then .ok (.str (c - 0x80), pos + 1)
    else if c < 0xc0 then
      match longLengthB b (c - 0xb7) (pos + 1) lim with
      | .error e => .error e
      | .ok (n, q) => .ok (.str n, q)
    else if c < 0xf8 then .ok (.list (c - 0xc0), pos + 1)
    else
      match longLengthB b (c - 0xf7) (pos + 1) lim with
      | .error e => .error e
      | .ok (n, q) => .ok (.list n, q)

mutual
/-- One item at `pos`, before `lim`, and the position after it. -/
def decodeItemB (b : ByteArray) : Nat → Nat → Nat → Except DecodeError (Item × Nat)
  | 0, _, _ => .error .malformed
  | n + 1, pos, lim =>
    match decodeHeadB b pos lim with
    | .error e => .error e
    | .ok (.single c, q) => .ok (.bytes [c], q)
    | .ok (.str len, q) =>
      if lim - q < len then .error .truncated
      else
        let p := Wire.slice b q (q + len)
        if isSingleLow p then .error .malformed else .ok (.bytes p, q + len)
    | .ok (.list len, q) =>
      if lim - q < len then .error .truncated
      else
        match decodeSeqB b n q (q + len) with
        | .error _ => .error .malformed
        | .ok is => .ok (.list is, q + len)

/-- Every item from `pos` to exactly `lim`. -/
def decodeSeqB (b : ByteArray) : Nat → Nat → Nat → Except DecodeError (List Item)
  | n, pos, lim =>
    if lim ≤ pos then .ok []
    else match n with
      | 0 => .error .malformed
      | n + 1 =>
        match decodeItemB b n pos lim with
        | .error e => .error e
        | .ok (i, q) =>
          match decodeSeqB b n q lim with
          | .error e => .error e
          | .ok is => .ok (i :: is)
end

/-- One valid item at the front of `b`, and the number of bytes it
took. The fuel is the model's, `fuel (toNatList b)`. -/
def decodeB? (b : ByteArray) : Except DecodeError (Value × Nat) :=
  match decodeItemB b (2 * b.size + 2) 0 b.size with
  | .error e => .error e
  | .ok (i, q) => if h : i.valid = true then .ok (⟨i, h⟩, q) else .error .malformed

/-- The wire bytes of a value. -/
def encodeB (v : Value) : ByteArray := ofNatList (encode v.item)

end Libp2p.Identity.Rlp
