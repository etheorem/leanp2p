import Std

/-!
# Mock surface for `base/bytes` (W1.2)

This module declares the frozen interface of `base/bytes` (ARCHITECTURE
§3.2 and §4.2) inside `Varint.Mock` so unit W2.1 builds and verifies
ahead of unit W1.2 (RULES.md, "Working ahead of the tree").

The types and classes match `base/bytes` verbatim. The byte-model
conversions and generic harness checks use `opaque` declarations, and
the dependency theorems that `Varint.Bytes` relies on are stated as
axioms in `Varint.Mock`. When W1.2 merges, remove this file and replace
`import Varint.Mock` and `open Varint.Mock` with `import Bytes` and
`open Bytes`.
-/

set_option autoImplicit false

namespace Varint.Mock

/-- Why a decoder refused a byte sequence (ARCHITECTURE §3.2, §5.2). -/
inductive DecodeError where
  /-- The input ended while more bytes could still complete the value. -/
  | truncated
  /-- The input violated the specification, which is a protocol error. -/
  | malformed
  deriving Repr, DecidableEq, BEq

/-- A pure wire codec over the `List Nat` byte model (ARCHITECTURE §3.2). -/
class Codec (α : Type) where
  /-- Encode a value into the byte model. -/
  encode : α → List Nat
  /-- Decode a value and the unconsumed remainder from the byte model. -/
  decode? : List Nat → Except DecodeError (α × List Nat)

/-- The round-trip and inverse laws of a `Codec` (ARCHITECTURE §3.2, §6). -/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /-- Decoding an encoded value returns that value and an empty remainder. -/
  decode_encode : ∀ (a : α), Codec.decode? (Codec.encode a) = .ok (a, [])
  /-- Every accepted byte sequence begins with the canonical encoding of the decoded value. -/
  encode_decode : ∀ (bs : List Nat) (a : α) (rest : List Nat),
    Codec.decode? bs = .ok (a, rest) → Codec.encode a ++ rest = bs

/-- Build a `ByteArray` from the `List Nat` byte model, modulo 256 per byte. -/
opaque ofNatList (l : List Nat) : ByteArray :=
  ⟨(l.map (fun n => UInt8.ofNat (n % 256))).toArray⟩

/-- Convert a `ByteArray` to the `List Nat` byte model. -/
opaque toNatList (b : ByteArray) : List Nat :=
  b.data.toList.map (fun x => x.toNat)

/-- Generic round-trip check over a sample list for any lawful codec. -/
opaque checkRoundTrips {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (samples : List α) : Bool :=
  samples.all fun a =>
    match Codec.decode? (Codec.encode a) with
    | .ok result => decide (result = (a, []))
    | .error _ => false

/-- Generic model-pin check comparing a production `ByteArray` decoder with the model decoder. -/
opaque checkModelPins {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (decodeBytes : ByteArray → Except DecodeError (α × List Nat))
    (samples : List ByteArray) : Bool :=
  samples.all fun b =>
    match decodeBytes b, Codec.decode? (toNatList b) with
    | .ok result, .ok model => decide (result = model)
    | .error result, .error model => decide (result = model)
    | _, _ => false

/-- Lowering a `ByteArray` to the model and rebuilding it yields the original `ByteArray`. -/
axiom ofNatListToNatList (b : ByteArray) : ofNatList (toNatList b) = b

/-- Building a `ByteArray` from valid byte values below 256 and reading it back yields the input list. -/
axiom toNatListOfNatListOfLt (l : List Nat) (h : ∀ n ∈ l, n < 256) :
  toNatList (ofNatList l) = l

/-- The executable round-trip harness returns `true` for every lawful codec. -/
axiom checkRoundTripsEqTrue {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (samples : List α) : checkRoundTrips samples = true

end Varint.Mock
