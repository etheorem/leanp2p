import Crypto
import Multiformats
import Proto
import Libp2p.Identity.KeyType

/-!
# The identity error

`Identity.Error` is the one error inductive of the package (ARCHITECTURE
§3.5). Each arm names one boundary: the protobuf of a key, the per-type
`Data` check, the crypto facade, and the peer id text or bytes. The
arms carry the error of the layer below verbatim, so a caller can still
tell a cut input (`truncated`) from a broken one.
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-- A failure of the identity package. -/
inductive Error where
  /-- The `Keys` protobuf did not decode at the wire level. -/
  | message (e : Pb.Error)
  /-- The `Keys` message lacks a required field, `Type` or `Data`; the
  arm carries the field number. -/
  | missingField (field : Nat)
  /-- The `Type` field holds a code outside the closed set of four. -/
  | badKeyType (code : Nat)
  /-- The `Data` bytes do not fit the key type: the size of a raw key
  or the DER shell (owned contract 2). The size is the one the input
  carried. -/
  | keyData (t : KeyType) (size : Nat)
  /-- An Ed25519 private `Data` whose public key is not the public key of
  its seed, or a legacy 96-byte form whose two public copies differ. The
  spec defines the envelope as the seed and its public key, and for the
  legacy form says to "reject or error out". -/
  | publicMismatch
  /-- The crypto facade failed: a key the backend does not load, or a
  library fault. -/
  | crypto (e : Crypto.CryptoError)
  /-- A peer id text or byte string did not decode: the multibase, CID,
  or multihash boundary of `codec/multiformats`. -/
  | peerIdCodec (e : Multiformats.Error)
  /-- A well-formed multihash that is not a peer id: neither identity
  nor sha2-256 with a 32-byte digest
  (`Multiformats.Multiaddr.validPeerHash`). -/
  | notPeerShape
  deriving DecidableEq, Repr, BEq

end Libp2p.Identity
