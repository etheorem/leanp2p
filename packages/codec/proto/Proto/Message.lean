import Proto.Bytes

/-!
# Message tables

A message type supplies its field table and validation. The generic
entry points share the wire codec. The message-specific types belong
to the packages above this one.
-/

set_option autoImplicit false

namespace Pb

/-- A message defines its table and checks the fields it understands. -/
class ProtoMessage (α : Type) where
  toFields : α → Fields
  ofFields? : Fields → Except Error α

/-- Model encoding follows the fixed emit order of the instance table. -/
def encodeMessage {α : Type} [ProtoMessage α] (message : α) : List Nat :=
  encodeFields (ProtoMessage.toFields message)

/-- Production encoding shares the table and the bounded wire representation. -/
def encodeMessageB {α : Type} [ProtoMessage α] (message : α) : ByteArray :=
  encodeFieldsB (ProtoMessage.toFields message)

/-- A valid wire message may still fail its message-specific validation. -/
def decodeMessage? {α : Type} [ProtoMessage α] (bs : List Nat) :
    Except Error (α × List Nat) := do
  let (fs, rest) ← decodeFields? bs
  let value ← ProtoMessage.ofFields? fs
  .ok (value, rest)

/-- The consumed count remains visible to the caller. -/
def decodeMessageB? {α : Type} [ProtoMessage α] (bs : ByteArray) :
    Except Error (α × Nat) := do
  let (fs, used) ← decodeFieldsB? bs
  let value ← ProtoMessage.ofFields? fs
  .ok (value, used)

end Pb
