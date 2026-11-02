import Std

/-!
# Mock of `base/bytes`

The frozen surface of the byte floor (ARCHITECTURE §3.2), until W1.2
merges. This module stands in for the real package and imports nothing
from it (RULES.md, "Working ahead of the tree"). It declares the three
things the yamux package consumes: the shared `DecodeError`, the `Codec`
class, and the `LawfulCodec` law, plus the generic round-trip check the
suite runs.

When W1.2 merges, the import and the namespace move to `Bytes` and this
module goes away. The ledger on issue #25 records that connection.
-/

namespace Yamux.Mock.Bytes

/-- Why a decoder refused a byte sequence. -/
inductive DecodeError where
  /-- The input ended, and more bytes could still complete the value. -/
  | truncated
  /-- The input violated the specification. -/
  | malformed
  deriving Repr, DecidableEq, BEq, Hashable

/-- A pure wire codec over the byte model. -/
class Codec (α : Type) where
  /-- The bytes this value encodes to. -/
  encode : α → List Nat
  /-- Read a value, and the bytes left after it. -/
  decode? : List Nat → Except DecodeError (α × List Nat)

/-- The round-trip law of a `Codec`. -/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /-- Decoding an encoded value returns that value and no leftover. -/
  decodeEncode : ∀ (a : α), Codec.decode? (Codec.encode a) = .ok (a, [])
  /-- Every accepted input is the encoding of the decoded value. -/
  encodeDecode : ∀ (bs : List Nat) (a : α) (rest : List Nat),
    Codec.decode? bs = .ok (a, rest) → Codec.encode a ++ rest = bs

/-- The model as production bytes: one byte per value, taken mod 256. -/
def ofNatList (l : List Nat) : ByteArray :=
  ByteArray.mk (l.map (fun n => UInt8.ofNat n)).toArray

/-- The production bytes as the model. -/
def toNatList (b : ByteArray) : List Nat :=
  b.toList.map (fun x => x.toNat)

/-- Check generated values with executable equality. -/
def checkRoundTrips {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (samples : List α) : Bool :=
  samples.all fun a =>
    match Codec.decode? (Codec.encode a) with
    | .ok result => decide (result = (a, []))
    | .error _ => false

end Yamux.Mock.Bytes
