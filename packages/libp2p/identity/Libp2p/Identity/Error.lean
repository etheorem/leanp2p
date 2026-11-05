import Libp2p.Identity.KeyType
import Proto
import Crypto
import Multiformats.Error

/-!
# Identity errors

Public identity boundaries retain dependency failures and distinguish key
validation from peer-id validation (root ARCHITECTURE §3.5).
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-- One package error type for key construction, crypto, and peer-id codecs. -/
inductive Error where
  | protobuf (error : Pb.Error)
  | missingField (number : Nat)
  | unknownKeyType (code : Nat)
  | invalidKeyData (keyType : KeyType) (size : Nat)
  | publicMismatch
  | crypto (error : Crypto.CryptoError)
  | encoding (error : Multiformats.Error)
  | invalidMultihash | invalidCid | textTooLong
  deriving BEq, DecidableEq, Repr

/-- The generic protobuf class can retain wire errors; validation maps to badField. -/
def Error.toProtobuf : Error → Pb.Error
  | .protobuf error => error
  | _ => .badField

end Libp2p.Identity
