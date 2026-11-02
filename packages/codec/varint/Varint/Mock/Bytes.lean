/-!
# Mock: the surface of `base/bytes`

W1.2 (`base/bytes`) is still open, so this package builds against a
mock of its frozen surface (RULES.md, "Working ahead of the tree";
ARCHITECTURE §4.2 and §3.2). The mock imports nothing from `Bytes`.
When W1.2 merges, the package drops this module, and each `open` of
`Varint.Mock.Bytes` becomes an `open` of `Bytes`.

The mock takes one of three forms for each name:

* **A function is `opaque`, with a body.** The compiler runs the body,
  so the tests see real bytes. The kernel cannot unfold an `opaque`
  constant, so no proof of this package can depend on the body.
* **A type or a class is a copy.** An `opaque` type has no
  constructors and a class has fields, so this module repeats the
  frozen shapes as the package docs of `base/bytes` give them.
* **The harness is a copy.** ARCHITECTURE §4.2 freezes "the generic
  round-trip harness" and no names. So the names and the types of
  `checkRoundTrips` and `checkModelPins`, and the field names of
  `LawfulCodec`, follow the open W1.2 pull request,
  etheorem/leanp2p#30. The tests use the same calls before and after
  the swap.

The mock states no axiom. The varint proofs work on `List Nat` alone,
so they need no fact about the byte model.
-/

set_option autoImplicit false

namespace Varint.Mock.Bytes

/-! ## The byte model -/

/-- One byte per model value, each value taken mod 256. -/
opaque ofNatList (l : List Nat) : ByteArray :=
  ⟨(l.map fun n => UInt8.ofNat (n % 256)).toArray⟩

/-- The model view of a byte array: one `Nat` below 256 per byte. -/
opaque toNatList (b : ByteArray) : List Nat :=
  b.data.toList.map UInt8.toNat

/-- The bytes that a lowercase hex string spells: two digits per byte.
`none` for an odd length, or for a character outside `0..9` and
`a..f`. -/
opaque ofHex? (s : String) : Option ByteArray :=
  let digit? (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else none
  let rec go : List Char → Option (List Nat)
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => do
      let h ← digit? hi
      let l ← digit? lo
      let tail ← go rest
      pure ((h * 16 + l) :: tail)
  (go s.toList).map fun l => ⟨(l.map UInt8.ofNat).toArray⟩

/-! ## The shared decode error -/

/-- The answer of a failed decode. `truncated` means that more bytes may
complete the value. `malformed` means a protocol error: no suffix can
repair the input. -/
inductive DecodeError where
  /-- The input ended before the value completed. -/
  | truncated
  /-- The input breaks the spec. -/
  | malformed
  deriving Repr, DecidableEq, BEq, Hashable

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

end Varint.Mock.Bytes
