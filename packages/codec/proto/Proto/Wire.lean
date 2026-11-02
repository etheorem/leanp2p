import Proto.Mock.Varint

/-!
# Ordered protobuf fields

The wire types 0, 1, 2 and 5 have constructors. A field list keeps its
wire order and duplicates. Its proof field carries the integer budgets
and byte validity, so serializing a `Fields` needs no extra hypothesis.
-/

set_option autoImplicit false

namespace Pb

open Mock.Bytes (DecodeError)

/-- Failures retain the distinction between incomplete and invalid framing. -/
inductive Error where
  | framing (reason : DecodeError)
  | badField
  | badWireType
  deriving DecidableEq, BEq, Repr

/-- Groups (wire types 3 and 4) are absent from the supported wire model. -/
inductive Value where
  | varint (value : Nat)
  | fixed64 (value : Nat)
  | bytes (payload : List Nat)
  | fixed32 (value : Nat)
  deriving DecidableEq, BEq, Repr

/-- Each constructor owns its wire discriminant. -/
def Value.wireType : Value → Nat
  | .varint _ => 0
  | .fixed64 _ => 1
  | .bytes _ => 2
  | .fixed32 _ => 5

/-- Byte validity is needed for the model-to-ByteArray conversion to preserve values. -/
def Value.Valid : Value → Prop
  | .varint n => n < Mock.Varint.limit
  | .fixed64 n => n < 256 ^ 8
  | .bytes bs => bs.length < Mock.Varint.limit ∧ ∀ b ∈ bs, b < 256
  | .fixed32 n => n < 256 ^ 4

instance (v : Value) : Decidable v.Valid := by
  cases v <;> unfold Value.Valid <;> infer_instance

/-- A raw entry is validated at the boundary. -/
abbrev Entry := Nat × Value

/-- Three wire-type bits leave 29 bits for the nonzero field number. -/
def fieldNumberLimit : Nat := 2 ^ 29

/-- The protobuf field number occupies the upper 29 bits of a uint32 tag. -/
def Entry.Valid (e : Entry) : Prop :=
  0 < e.1 ∧ e.1 < fieldNumberLimit ∧ e.2.Valid

instance (e : Entry) : Decidable e.Valid := inferInstanceAs
  (Decidable (0 < e.1 ∧ e.1 < fieldNumberLimit ∧ e.2.Valid))

/-- The wire representation preserves order; the proof carries all encoding bounds. -/
structure Fields where
  entries : List Entry
  valid : ∀ e ∈ entries, e.Valid

instance : BEq Fields where
  beq a b := a.entries == b.entries

instance : Repr Fields where
  reprPrec fs p := reprPrec fs.entries p

/-- Proof fields do not change equality of wire values. -/
@[ext] theorem Fields.ext {a b : Fields} (h : a.entries = b.entries) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- A checked constructor for callers building field tables. -/
def Fields.ofList? (entries : List Entry) : Except Error Fields :=
  if h : ∀ e ∈ entries, e.Valid then .ok ⟨entries, h⟩
  else .error .badField

/-- The empty message has an empty encoding. -/
def Fields.empty : Fields := ⟨[], by simp⟩

/-- Shared-codec callers see the coarse error; wire callers retain the detailed one. -/
def Error.toDecodeError : Error → DecodeError
  | .framing e => e
  | .badField | .badWireType => .malformed

end Pb
