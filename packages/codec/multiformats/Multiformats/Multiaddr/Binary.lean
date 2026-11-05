import Multiformats.Multiaddr.Core

/-!
# Multiaddr byte boundaries

The production reader uses cursor offsets and checks the complete input
budget before reading any component. An address occupies its entire
externally framed message; no accepted suffix is silently discarded.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

/-- The model byte view is the one used by the codec theorems. -/
def toBytes (address : Multiaddr) : List Nat := encode address

/-- The model boundary accepts one complete canonical address. -/
def ofBytes? (input : List Nat) : Except Error Multiaddr := Prod.fst <$> decode? input

/-- The production encoder writes directly into a single byte builder. -/
def toByteArray (address : Multiaddr) : ByteArray := SequenceWire.encodeFramesB address.frames

/-- The cursor reader reports its complete consumed length for framed callers. -/
def decodeB? (input : ByteArray) : Except Error (Multiaddr × Nat) := do
  if input.size > maxAddressBytes then .error .overCap
  else
    let (wire, used) ← SequenceWire.decodeB? acceptFrames input
    if used = input.size then .ok (⟨wire⟩, used) else .error .badAddress

/-- A standalone byte decode validates exact input consumption. -/
def ofByteArray? (input : ByteArray) : Except Error Multiaddr := Prod.fst <$> decodeB? input

end Multiformats.Multiaddr
