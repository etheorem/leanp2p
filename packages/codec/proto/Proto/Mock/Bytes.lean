import Std

/-!
# Temporary byte interface

W1.2 is not merged. This module isolates its documented surface under
`Pb.Mock.Bytes`. The conversions have executable bodies so fixtures can
run. The classes state the two laws from the frozen byte contract.
Replace this module with the real imports when W1.2 lands.
-/

set_option autoImplicit false

namespace Pb.Mock.Bytes

/-- A short input can grow; a malformed input must be rejected. -/
inductive DecodeError where
  | truncated
  | malformed
  deriving DecidableEq, BEq, Repr

/-- A pure codec returns the decoded value and the unconsumed suffix. -/
class Codec (α : Type) where
  encode : α → List Nat
  decode? : List Nat → Except DecodeError (α × List Nat)

/-- Both directions of the byte contract. The inverse includes the suffix. -/
class LawfulCodec (α : Type) [Codec α] : Prop where
  decodeEncode : ∀ a : α, Codec.decode? (Codec.encode a) = .ok (a, [])
  encodeDecode : ∀ (bs : List Nat) (a : α) (rest : List Nat),
    Codec.decode? bs = .ok (a, rest) → bs = Codec.encode a ++ rest

/-- The model-to-byte conversion specified by W1.2 reduces entries modulo 256. -/
opaque ofNatList (bs : List Nat) : ByteArray :=
  (bs.map UInt8.ofNat).toByteArray

/-- ByteArray inputs always yield byte-valued model entries. -/
opaque toNatList (bs : ByteArray) : List Nat := bs.toList.map UInt8.toNat

/-- UTF-8 validity belongs to the byte dependency. -/
opaque toString? (bs : ByteArray) : Option String := String.fromUTF8? bs

/-- Temporary generic model pin until the W1.2 harness API lands. -/
def productionAgrees {α : Type} [Codec α] [BEq α]
    (decodeB : ByteArray → Except DecodeError (α × Nat)) (bs : ByteArray) : Bool :=
  match Codec.decode? (toNatList bs), decodeB bs with
  | .ok (a, rest), .ok (b, used) => a == b && used + rest.length == bs.size
  | .error a, .error b => a == b
  | _, _ => false

/-- One generic roundtrip loop; the codec package supplies its values and byte decoder. -/
def checkCodec {α : Type} [Codec α] [LawfulCodec α] [BEq α]
    (decodeB : ByteArray → Except DecodeError (α × Nat)) (samples : List α) : Bool :=
  samples.all fun a =>
    let bs := Codec.encode a
    let modelOk := match Codec.decode? bs with
      | .ok (b, rest) => a == b && rest.isEmpty
      | .error _ => false
    modelOk && productionAgrees decodeB (ofNatList bs)

end Pb.Mock.Bytes
