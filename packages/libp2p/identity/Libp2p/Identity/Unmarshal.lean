import Libp2p.Identity.Keys

/-!
# The strict unmarshal

A marshaled key arrives from a peer (the Noise payload, identify) or
from storage. The unmarshal decodes the `Keys` message, then checks the
`Data` against the key type, before anything derives from the key
(§4.9, §5.2; PRINCIPLES 2.4). The spike records why the order matters:
a truncated key would still derive a well-formed but bogus peer id.

The per-type check is the key constructor, `PubKey.ofKeys?` or
`PrivKey.ofKeys?`; the `ProtoMessage` instances run the same one. This
module keeps the precise `Identity.Error` of a failure, where the
instances report a `Pb.Error`.
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-- The `Keys` message of marshaled bytes. -/
def Keys.unmarshal? (b : ByteArray) : Except Error Keys := do
  let (fs, _) ← (Pb.decodeFieldsB? b).mapError .message
  Keys.ofFields? fs

/-- The strict unmarshal of a public key: the message, then the `Data`
check. -/
def PubKey.unmarshal? (b : ByteArray) : Except Error PubKey := do
  ofKeys? (← Keys.unmarshal? b)

/-- The strict unmarshal of a private key: the message, then the `Data`
check, with the Ed25519 forms made canonical first. -/
def PrivKey.unmarshal? (b : ByteArray) : Except Error PrivKey := do
  ofKeys? (← Keys.unmarshal? b)

end Libp2p.Identity
