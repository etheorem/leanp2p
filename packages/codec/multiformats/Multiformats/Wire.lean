import Multiformats.Mock.Varint
import Multiformats.Error

/-!
# Shared framing rules

Multihash, CID, and address components share the same bounded varints
and payload checks. The model rejects entries that cannot be bytes.
-/

set_option autoImplicit false

namespace Multiformats.Wire

open Mock

/-- Valid callers are unchanged; the modulo keeps the helper total on Nat. -/
def toVarint (n : Nat) : Varint.UVarint :=
  ⟨n % Varint.limit, Nat.mod_lt _ (by decide)⟩

/-- A bounded dependency value is already in the helper's range. -/
theorem toVarintVal (value : Varint.UVarint) : toVarint value.val = value := by
  cases value with
  | mk n h => simp only [toVarint, Nat.mod_eq_of_lt h]

/-- Integer framing has one encoder. -/
def encodeNat (n : Nat) : List Nat := Varint.encode (toVarint n)

/-- The byte builder writes one group per step, without a model-list allocation. -/
private def writeNatCore (value : Nat) (output : ByteArray) : ByteArray :=
  if value < 128 then output.push (UInt8.ofNat value)
  else writeNatCore (value / 128) (output.push (UInt8.ofNat (value % 128 + 128)))
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- The production path follows the same bounded-integer domain as the model. -/
def writeNatB (value : Nat) (output : ByteArray) : ByteArray :=
  writeNatCore (value % Varint.limit) output

/-- Validated payload bytes are appended directly to a byte builder. -/
def writeBytesB (bytes : List Nat) (output : ByteArray) : ByteArray :=
  bytes.foldl (fun acc byte => acc.push (UInt8.ofNat byte)) output

/-- A cap is checked before either traversal or extraction of the payload. -/
def takeBytes (cap count : Nat) (input : List Nat) : Except Error (List Nat × List Nat) :=
  if count > cap then .error .overCap
  else if ∀ b ∈ input.take count, b < 256 then
    if (input.take count).length < count then .error (.framing .truncated)
    else .ok (input.take count, input.drop count)
  else .error (.framing .malformed)

/-- Valid encoded payloads are read without consuming the suffix. -/
theorem takeBytesAppend (cap : Nat) (payload rest : List Nat)
    (hcap : payload.length ≤ cap) (hbytes : ∀ b ∈ payload, b < 256) :
    takeBytes cap payload.length (payload ++ rest) = .ok (payload, rest) := by
  unfold takeBytes
  simp only [show ¬ payload.length > cap by omega, ite_false,
    List.take_left, List.drop_left]
  split
  · split
    · rename_i hshort
      omega
    · rfl
  · rename_i invalid
    exact (invalid hbytes).elim

/-- Every successful read accounts for its length, bytes, cap, and suffix. -/
theorem takeBytesOk (cap count : Nat) (input payload rest : List Nat)
    (h : takeBytes cap count input = .ok (payload, rest)) :
    payload.length = count ∧ (∀ b ∈ payload, b < 256) ∧
      count ≤ cap ∧ input = payload ++ rest := by
  unfold takeBytes at h
  split at h
  · cases h
  · rename_i hcap
    split at h
    · rename_i hbytes
      split at h
      · cases h
      · rename_i hlen
        have hp := Prod.mk.inj (Except.ok.inj h)
        rcases hp with ⟨rfl, rfl⟩
        refine ⟨?_, hbytes, by omega, (List.take_append_drop count input).symm⟩
        simp only [List.length_take] at hlen ⊢
        omega
    · cases h

/-- The production dependency sees a budget-sized window instead of the whole tail. -/
def readVarintAt (input : ByteArray) (position : Nat) :
    Except Error (Varint.UVarint × Nat) := do
  let window := input.extract position (min input.size (position + Varint.maxBytes))
  let (value, used) ← (Varint.decodeB? window).mapError Error.framing
  .ok (value, position + used)

/-- The available size is checked before a variable-length extraction. -/
def takeBytesAt (input : ByteArray) (position count cap : Nat) :
    Except Error (List Nat × Nat) :=
  if count > cap then .error .overCap
  else if position + count > input.size then .error (.framing .truncated)
  else .ok ((input.extract position (position + count)).toList.map UInt8.toNat,
    position + count)

end Multiformats.Wire
