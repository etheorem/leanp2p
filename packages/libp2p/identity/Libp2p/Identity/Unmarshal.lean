import Libp2p.Identity.Error
import Libp2p.Identity.Marshal
import Bytes
import Proto

/-!
# Key deserialization

The protobuf library checks the byte framing. This module reads Type and
Data, then delegates key validity to the checked constructor supplied by
`Keys`. Taking that constructor as an argument avoids an import cycle and
keeps the validity rules out of the decoder.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Unmarshal

/-- Interpret Type/Data and call the key's checked constructor.
Unknown fields are ignored; singular fields use protobuf's last-wins lookup. -/
def keyFields? {α : Type} (ofData? : KeyType → ByteArray → Except Error α)
    (fields : Pb.Fields) : Except Error α := do
  let some code := Pb.getVarint? 1 fields | throw (.missingField 1)
  let some keyType := KeyType.ofCode? code | throw (.unknownKeyType code)
  let some raw := Pb.getBytes? 2 fields | throw (.missingField 2)
  ofData? keyType (Bytes.ofNatList raw)

/-- Decode the complete buffer, preserving the constructor's precise error. -/
def key? {α : Type} (ofData? : KeyType → ByteArray → Except Error α)
    (bytes : ByteArray) : Except Error α := do
  let (fields, _) ← (Pb.decodeFieldsB? bytes).mapError Error.protobuf
  keyFields? ofData? fields

/-- Field extraction recovers the original type and bytes before validation. -/
theorem keyFieldsRoundTrip {α : Type} (ofData? : KeyType → ByteArray → Except Error α)
    (keyType : KeyType) (raw : ByteArray)
    (valid : (Pb.Value.bytes (Bytes.toNatList raw)).Valid) :
    keyFields? ofData? (Marshal.keyFields keyType raw valid) = ofData? keyType raw := by
  simp [keyFields?, Marshal.keyFields, Pb.getVarint?, Pb.getBytes?, Pb.lookupLast,
    List.lookup, KeyType.ofCode?_toCode, Bytes.ofNatListToNatList]


end Libp2p.Identity.Unmarshal
