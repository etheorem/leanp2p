import Varint.UVarint

/-!
# The varint theorems

The theorems over the model beyond the instance law (the package
ARCHITECTURE, "Theorems"; ARCHITECTURE §6), and the spec examples.

Two theorems of the package live in `Varint.UVarint`, because the proof
of the instance law uses them: the suffix form `decodeEncodeSuffix` and
the budget lemma `lengthEncodeLe`. Each fact has one name.
-/

set_option autoImplicit false

namespace Varint

open Varint.Mock.Bytes

/-- The accepted-input split: a successful decode consumed exactly the
encoding of its value, and the rest is the input after it. No other
byte string decodes to the same value, since the decoder accepts
minimal encodings only. This is the `encodeDecode` law of the instance,
stated over `decode?` so a framing layer can rewrite the input with
it. -/
theorem encodeDecode {bs rest : List Nat} {v : UVarint}
    (h : decode? bs = .ok (v, rest)) : bs = encode v ++ rest :=
  (LawfulCodec.encodeDecode bs v rest h).symm

/-- Every encoding holds at least one byte, so a decode always consumes
input. -/
theorem encodeNonempty (v : UVarint) : encode v ≠ [] := by
  unfold encode
  rw [encodeNat]
  split <;> simp

/-- Every entry of an encoding is a byte, so `ofNatList` writes the
model unchanged to the wire. -/
theorem encodeBytes (v : UVarint) : ∀ b ∈ encode v, b < 256 :=
  fun _ hb => ltOfMemEncodeNat hb

/-! ## The spec examples

The examples of `vendor/unsigned-varint/README.md`, lines 32 to 37.
`encodeNat` recurses by well-founded recursion, which the kernel does
not unfold, so `decide` cannot evaluate it; `simp [encodeNat]` unfolds
it through its equation lemma instead. `decodeGroups` recurses on the
list, so `rfl` evaluates it in the kernel. -/

example : encodeNat 1 = [0x01] := by simp [encodeNat]
example : encodeNat 127 = [0x7F] := by simp [encodeNat]
example : encodeNat 128 = [0x80, 0x01] := by simp [encodeNat]
example : encodeNat 255 = [0xFF, 0x01] := by simp [encodeNat]
example : encodeNat 300 = [0xAC, 0x02] := by simp [encodeNat]
example : encodeNat 16384 = [0x80, 0x80, 0x01] := by simp [encodeNat]
example : encodeNat 0 = [0x00] := by simp [encodeNat]

-- The rejections, on the model core.
example : decodeGroups 0 [0x80, 0x00] = .error .malformed := rfl
example : decodeGroups 0 [0x81, 0x00] = .error .malformed := rfl
example : decodeGroups 0 [0x80] = .error .truncated := rfl
example : decodeGroups 0 (List.replicate 9 0x80) = .error .malformed := rfl
example : decodeGroups 0 (List.replicate 8 0x80) = .error .truncated := rfl
example : decodeGroups 0 [0x100] = .error .malformed := rfl

end Varint
