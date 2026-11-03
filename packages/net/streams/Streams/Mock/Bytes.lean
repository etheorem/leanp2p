/-!
# Mock: the surface of `base/bytes`

W1.2 (`base/bytes`) is still open, so this package builds against a
mock of its frozen surface (RULES.md, "Working ahead of the tree";
ARCHITECTURE §4.2 and §3.2). The mock imports nothing from `Bytes`.
When W1.2 merges, the package drops this module, and each `open` of
`Streams.Mock.Bytes` becomes an `open` of `Bytes`.

The mock takes one of three forms for each name:

* **A function is `opaque`, with a body.** The compiler runs the body,
  so the tests see real bytes. The kernel cannot unfold an `opaque`
  constant, so no proof of this package can depend on the body. A
  proof that needs a fact about the function states it as an axiom.
* **A type, a class, or a structure is a copy.** An `opaque` type has
  no constructors and a class has fields, so this module repeats the
  frozen shapes as the package docs of `base/bytes` give them.
* **The harness is a copy.** ARCHITECTURE §4.2 freezes "the generic
  round-trip harness" and no names. So the names and the types of
  `checkRoundTrips` and `checkModelPins`, and the field names of
  `LawfulCodec`, follow the open W1.2 pull request,
  etheorem/leanp2p#30. The tests use the same calls before
  and after the swap.

The mock states no axiom. The framing proofs need no fact about the
byte model, since they work on `List Nat` alone.
-/

set_option autoImplicit false

namespace Streams.Mock.Bytes

/-! ## The byte model -/

/-- One byte per model value, each value taken mod 256. -/
opaque ofNatList (l : List Nat) : ByteArray :=
  ⟨(l.map UInt8.ofNat).toArray⟩

/-- The model view of a byte array: one `Nat` below 256 per byte. -/
opaque toNatList (b : ByteArray) : List Nat :=
  b.data.toList.map UInt8.toNat

/-! ## The shared decode error -/

/-- The answer of a failed decode. `truncated` means that more bytes may
complete the value. `malformed` means a protocol error: no suffix can
repair the input. -/
inductive DecodeError where
  /-- The input ended before the value completed. -/
  | truncated
  /-- The input breaks the spec. -/
  | malformed
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ## The codec classes -/

/-- A pure wire codec over the byte model (ARCHITECTURE §3.2). -/
class Codec (α : Type) where
  /-- The wire bytes of a value. -/
  encode : α → List Nat
  /-- One value from the front of the input, and the rest of the
  input. -/
  decode? : List Nat → Except DecodeError (α × List Nat)

/-- The round-trip law of a codec. -/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /-- The encoding of a value decodes to the value, and no input
  remains. -/
  decodeEncode : ∀ a : α, Codec.decode? (Codec.encode a) = .ok (a, [])
  /-- A successful decode re-encodes to its input. -/
  encodeDecode : ∀ (bs : List Nat) (a : α) (rest : List Nat),
    Codec.decode? bs = .ok (a, rest) → Codec.encode a ++ rest = bs

/-! ## The harness -/

/-- Every lawful codec reads back exactly the bytes that it writes. -/
theorem codecRoundTrip {α : Type} [Codec α] [LawfulCodec α] (a : α) :
    Codec.decode? (Codec.encode a) = .ok (a, []) :=
  LawfulCodec.decodeEncode a

/-- The round trip on the sample values, checked with executable
equality. -/
def checkRoundTrips {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (samples : List α) : Bool :=
  samples.all fun a =>
    match Codec.decode? (Codec.encode a) with
    | .ok result => decide (result = (a, []))
    | .error _ => false

/-- The model pin: the production decoder answers as `Codec.decode?`
answers on the model view of each sample. Before the check, the caller
changes the rest of the production answer to its model view. -/
def checkModelPins {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (decodeBytes : ByteArray → Except DecodeError (α × List Nat))
    (samples : List ByteArray) : Bool :=
  samples.all fun b =>
    match decodeBytes b, Codec.decode? (toNatList b) with
    | .ok result, .ok model => decide (result = model)
    | .error result, .error model => decide (result = model)
    | _, _ => false

end Streams.Mock.Bytes
