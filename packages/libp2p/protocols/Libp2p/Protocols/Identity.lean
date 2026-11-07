import Bytes
import Libp2p.Identity

/-!
# The boundary to `libp2p/identity`

Identify carries its fields over the `List Nat` byte model, and the
identity package speaks `ByteArray`. This module holds the three
conversions: parse the `publicKey` field, derive the peer id of a key,
and serialize a key back to the wire.

`libp2p/identity` landed as W5.1, so the conversions call the real
package. The module replaces the earlier identity mock, and it keeps the
signatures the pure half already names.
-/

set_option autoImplicit false

namespace Libp2p.Protocols

/-- Parse the `publicKey` field. The field is the serialized `PublicKey`
protobuf (`PublicKey.unmarshal?`). -/
def unmarshalPubKey? (bs : List Nat) : Option Libp2p.Identity.PubKey :=
  (Libp2p.Identity.PubKey.unmarshal? (Bytes.ofNatList bs)).toOption

/-- The peer id of a key. A key at the inline threshold gives an inline
id, and a longer key takes the facade's SHA-256, which fails only on a
crypto fault; the error arm keeps the identity of the empty key. The
validate path only reaches a key that parsed, so the error arm cannot
change an accepted record. -/
def peerIdOfPubKey (k : Libp2p.Identity.PubKey) : Libp2p.Identity.PeerId :=
  match Libp2p.Identity.PeerId.ofPubKey k with
  | .ok p => p
  | .error _ =>
      Libp2p.Identity.PeerId.inline ByteArray.empty (by
        simp [ByteArray.size, Libp2p.Identity.maxInlineKeyBytes])

/-- Serialize a key to the wire form the `publicKey` field carries. -/
def marshalPubKey (k : Libp2p.Identity.PubKey) : List Nat :=
  Bytes.toNatList k.marshal

end Libp2p.Protocols
