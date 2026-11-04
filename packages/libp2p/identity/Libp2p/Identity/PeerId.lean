import Libp2p.Identity.Keys
import Crypto
import Multiformats

/-!
# Peer IDs

The peer-ids specification derives an identity from the complete public-key
protobuf. At most 42 bytes inline; larger keys use SHA-256. The text boundary
accepts legacy base58btc and multibase CIDv1 with the libp2p-key codec.
Each value carries the peer-multihash check and its chosen print form.

-/

set_option autoImplicit false

namespace Libp2p.Identity

open Multiformats

namespace PeerId

/-- The identity owns the accepted hash functions and SHA-256 digest size. -/
def Valid (hash : Multihash) : Prop :=
  hash.code = 0 ∨ (hash.code = 0x12 ∧ hash.length = peerIdDigestSize)

instance (hash : Multihash) : Decidable (Valid hash) :=
  inferInstanceAs (Decidable (hash.code = 0 ∨
    (hash.code = 0x12 ∧ hash.length = peerIdDigestSize)))

/-- Parsing records the alphabet so printing preserves the accepted string. -/
inductive TextForm where
  | legacy
  | cid (base : Multibase.Base)
  deriving DecidableEq, BEq, Hashable, Ord, Repr

/-- Keep dependency failures distinct from peer-specific shape rejections. -/
inductive Error where
  | encoding (error : Multiformats.Error)
  | crypto (error : Crypto.CryptoError)
  | invalidMultihash | invalidCid | textTooLong
  deriving BEq, DecidableEq, Repr

end PeerId

/-- A checked peer multihash, with the representation chosen at its boundary. -/
structure PeerId where
  multihash : Multihash
  valid : PeerId.Valid multihash
  textForm : PeerId.TextForm := .legacy
  deriving DecidableEq, Repr

/-- Runtime equality identifies peers independently of their text representation.
Structural equality still includes `textForm`, so this is not `LawfulBEq`. -/
instance : BEq PeerId := ⟨fun left right => left.multihash == right.multihash⟩

/-- Peerstore keys hash the same identity equally across text forms. -/
instance : Hashable PeerId := ⟨fun peer => hash peer.multihash⟩

/-- Ordering uses the same identity as runtime equality, ignoring presentation. -/
instance : Ord PeerId := ⟨fun left right => compare left.multihash right.multihash⟩

namespace PeerId

/-- Check the peer-specific rule once, after the general multihash decoder. -/
def ofMultihash? (hash : Multihash) (form : TextForm := .legacy) : Except Error PeerId :=
  if h : Valid hash then .ok ⟨hash, h, form⟩ else .error .invalidMultihash

/-- Bare multihash bytes are the binary peer ID, without a CID wrapper. -/
def toBytes (peer : PeerId) : ByteArray := peer.multihash.toByteArray

/-- Binary input prints as legacy base58btc unless a text parser records a form. -/
def ofBytes? (bytes : ByteArray) : Except Error PeerId := do
  ofMultihash? (← Multihash.ofByteArray? bytes |>.mapError Error.encoding)

/-- Derive only from a checked public key; the threshold counts its whole envelope. -/
def ofPublicKey (key : PubKey) : Except Error PeerId := do
  let encoded := marshalPubKey key
  let hash ← if encoded.size ≤ maxInlineKeySize then
      Multihash.ofDigest? 0 encoded |>.mapError Error.encoding
    else do
      let digest ← Crypto.sha256 encoded |>.mapError Error.crypto
      Multihash.ofDigest? 0x12 digest |>.mapError Error.encoding
  ofMultihash? hash

/-- Explicit legacy conversion leaves the recorded form unchanged. -/
def toBase58 (peer : PeerId) : String := Base58.encode peer.toBytes

/-- Explicit CIDv1 conversion defaults to unpadded lower-case base32. -/
def toCidString (peer : PeerId) (base : Multibase.Base := .base32) : String :=
  Multibase.encode base (Cid.toByteArray (.v1 Cid.codecLibp2pKey peer.multihash))

/-- Print the stored representation; this operation is total on checked IDs. -/
def toString (peer : PeerId) : String :=
  match peer.textForm with
  | .legacy => peer.toBase58
  | .cid base => peer.toCidString base

instance : ToString PeerId := ⟨PeerId.toString⟩

/-- The legacy prefixes select bare multihash decoding; other forms require CIDv1. -/
def ofString? (text : String) : Except Error PeerId := do
  if text.length > maxPeerIdTextSize then throw .textTooLong
  if text.startsWith "1" || text.startsWith "Qm" then
    ofBytes? (← Base58.decode? text |>.mapError Error.encoding)
  else do
    let (base, bytes) ← Multibase.decode? text |>.mapError Error.encoding
    let cid ← Cid.ofByteArray? bytes |>.mapError Error.encoding
    match cid with
    | .v1 codec hash =>
        if codec != Cid.codecLibp2pKey then throw .invalidCid
        ofMultihash? hash (.cid base)
    | .v0 _ => throw .invalidCid

/-- The newtype exposes its checked invariant without a repeated runtime test. -/
theorem valid_multihash (peer : PeerId) : Valid peer.multihash := peer.valid

end PeerId

end Libp2p.Identity
