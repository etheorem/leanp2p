import Bytes.Error

/-!
# `Codec` and `LawfulCodec`

The two classes that every pure wire codec implements (ARCHITECTURE
§3.2). The model is the `List Nat` byte model of `Bytes.Model`: proofs
close on it with `omega`, and the production `ByteArray` path is pinned
to it by the harness of `Bytes.Harness`.

`LawfulCodec` states the round-trip law as a `Prop` class. Each
instance proves it, and one generic harness then runs for every
instance at once.
-/

set_option autoImplicit false

namespace Bytes

/-- A pure wire codec over the byte model. -/
class Codec (α : Type) where
  /-- The bytes this value encodes to. -/
  encode : α → List Nat
  /-- Read a value, and the bytes left after it, from the model. -/
  decode? : List Nat → Except DecodeError (α × List Nat)

/-- The round-trip law of a `Codec`.

The first field says a decode of an encode returns the value and eats
every byte. The second field says the encoder is the inverse on every
input that decodes, so a decoder never accepts a spelling that the
encoder would not produce. -/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /-- Decoding an encoded value returns that value and no leftover. -/
  decodeEncode : ∀ (a : α), Codec.decode? (Codec.encode a) = .ok (a, [])
  /-- Every accepted input is the encoding of the decoded value. -/
  encodeDecode : ∀ (bs : List Nat) (a : α) (rest : List Nat),
    Codec.decode? bs = .ok (a, rest) → Codec.encode a ++ rest = bs

end Bytes
