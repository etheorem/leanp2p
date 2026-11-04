import Libp2p.Identity.KeyType
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
def keyFields? {α : Type} (ofData? : KeyType → ByteArray → Option α)
    (fields : Pb.Fields) : Except Pb.Error α := do
  let some code := Pb.getVarint? 1 fields | throw .badField
  let some keyType := KeyType.ofCode? code | throw .badField
  let some raw := Pb.getBytes? 2 fields | throw .badField
  let some key := ofData? keyType (Bytes.ofNatList raw) | throw .badField
  pure key

/-- Decode one complete externally framed message through its `ProtoMessage` instance. -/
def key? {α : Type} [Pb.ProtoMessage α] (bytes : ByteArray) : Except Pb.Error α := do
  let (key, _) ← Pb.decodeMessageB? bytes
  pure key

end Libp2p.Identity.Unmarshal
