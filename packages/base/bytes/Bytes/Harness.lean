import Bytes.Codec
import Bytes.Model

/-!
# Shared codec checks

ARCHITECTURE §3.2 and §6 require one round-trip harness per codec.
Callers supply generated values and bytes. A production decoder adapter
returns the model remainder, so the pin compares values and errors too.
-/

set_option autoImplicit false

namespace Bytes

/-- Every lawful codec consumes exactly the bytes it writes. -/
theorem codecRoundTrip {α : Type} [Codec α] [LawfulCodec α] (a : α) :
    Codec.decode? (Codec.encode a) = .ok (a, []) :=
  LawfulCodec.decode_encode a

/-- Check generated values with executable equality. The proof instance
keeps each caller tied to the same two codec laws. -/
def checkRoundTrips {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (samples : List α) : Bool :=
  samples.all fun a =>
    match Codec.decode? (Codec.encode a) with
    | .ok result => decide (result = (a, []))
    | .error _ => false

/-- The runtime check `checkRoundTrips` answers true on every sample.

This is a consistency lemma between the executable check and the class law.
`checkRoundTrips` takes `[LawfulCodec α]` as an argument, so it cannot answer
false. Read it as a statement about the harness. The pin that constrains a
codec is `checkModelPins`, which compares a production decoder with the model. -/
theorem checkRoundTripsEqTrue {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (samples : List α) : checkRoundTrips samples = true := by
  simp [checkRoundTrips, codecRoundTrip]

/-- Compare the production decoder with its model on arbitrary bytes.
The caller adapts consumed lengths to remainders before this check. -/
def checkModelPins {α : Type} [Codec α] [LawfulCodec α] [DecidableEq α]
    (decodeBytes : ByteArray → Except DecodeError (α × List Nat))
    (samples : List ByteArray) : Bool :=
  samples.all fun b =>
    match decodeBytes b, Codec.decode? (toNatList b) with
    | .ok result, .ok model => decide (result = model)
    | .error result, .error model => decide (result = model)
    | _, _ => false

end Bytes