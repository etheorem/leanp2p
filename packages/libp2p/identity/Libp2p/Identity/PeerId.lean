import Libp2p.Identity.Keys
import Crypto
import Multiformats.Cid
import Multiformats.Multiaddr.Value

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

/-- Peer IDs and multiaddr's p2p component accept the same multihash shapes. -/
def Valid (hash : Multihash) : Prop :=
  Multiaddr.validPeerHash hash = true

instance (hash : Multihash) : Decidable (Valid hash) :=
  inferInstanceAs (Decidable (Multiaddr.validPeerHash hash = true))

/-- Keep the accepted CID spelling, including any case variations. -/
inductive TextForm where
  | legacy
  | cid (text : String)
  deriving DecidableEq, Repr

end PeerId

/-- A checked peer multihash, with the representation chosen at its boundary.
The private constructor keeps parsed text tied to the identity it decoded. -/
structure PeerId where
  private mk ::
  multihash : Multihash
  valid : PeerId.Valid multihash
  textForm : PeerId.TextForm := .legacy
  deriving DecidableEq, Repr

private def PeerId.identityKey (peer : PeerId) : Nat × List Nat :=
  (peer.multihash.code.toCode, peer.multihash.digest)

/-- Runtime equality identifies peers independently of their text representation.
Structural equality still includes `textForm`, so this is not `LawfulBEq`. -/
instance : BEq PeerId := ⟨fun left right => left.identityKey == right.identityKey⟩

/-- Peerstore keys hash the same identity equally across text forms. -/
instance : Hashable PeerId := ⟨fun peer => hash peer.identityKey⟩

/-- Ordering uses the same identity as runtime equality, ignoring presentation. -/
instance : Ord PeerId where
  compare left right :=
    -- Lean provides pair ordering as a value, so select it locally.
    letI : Ord (Nat × List Nat) := lexOrd
    compare left.identityKey right.identityKey

namespace PeerId

/-- Check the peer-specific rule once, after the general multihash decoder. -/
def ofMultihash? (hash : Multihash) : Except Error PeerId :=
  if h : Valid hash then .ok ⟨hash, h, .legacy⟩ else .error .invalidMultihash

/-- Bare multihash bytes are the binary peer ID, without a CID wrapper. -/
def toBytes (peer : PeerId) : ByteArray := peer.multihash.toByteArray

/-- Binary input prints as legacy base58btc unless a text parser records a form. -/
def ofBytes? (bytes : ByteArray) : Except Error PeerId := do
  ofMultihash? (← Multihash.ofByteArray? bytes |>.mapError Error.encoding)

/-- Derive only from a checked public key; the threshold counts its whole envelope. -/
def ofPublicKey (key : PubKey) : Except Error PeerId := do
  let encoded := marshalPubKey key
  let hash ← if encoded.size ≤ maxInlineKeySize then
      Multihash.ofDigest? .identity (Bytes.toNatList encoded) |>.mapError Error.encoding
    else do
      let digest ← Crypto.sha256 encoded |>.mapError Error.crypto
      Multihash.ofDigest? .«sha2-256» (Bytes.toNatList digest) |>.mapError Error.encoding
  ofMultihash? hash

/-- Explicit legacy conversion leaves the recorded form unchanged. -/
def toBase58 (peer : PeerId) : String := Base58.encode peer.toBytes

/-- Convert to a chosen CIDv1 base, reporting that base's encoding errors. -/
def toCidString? (peer : PeerId) (base : Multibase.Base) : Except Error String :=
  Multibase.encode base (Cid.toByteArray (.v1 .«p2p-key» peer.multihash))
    |>.mapError Error.encoding

/-- The default CIDv1 form is total, unpadded lower-case base32. -/
def toCidString (peer : PeerId) : String :=
  Multibase.encodeBase32 (Cid.toByteArray (.v1 .«p2p-key» peer.multihash))

/-- Print the stored representation; this operation is total on checked IDs. -/
def toString (peer : PeerId) : String :=
  match peer.textForm with
  | .legacy => peer.toBase58
  | .cid text => text

instance : ToString PeerId := ⟨PeerId.toString⟩

/-- The legacy prefixes select bare multihash decoding; other forms require CIDv1. -/
def ofString? (text : String) : Except Error PeerId := do
  if text.length > maxPeerIdTextSize then throw .textTooLong
  if text.startsWith "1" || text.startsWith "Qm" then
    ofBytes? (← Base58.decode? text |>.mapError Error.encoding)
  else do
    let (_, bytes) ← Multibase.decode? text |>.mapError Error.encoding
    let cid ← Cid.ofByteArray? bytes |>.mapError Error.encoding
    match cid with
    | .v1 .«p2p-key» hash =>
        let peer ← ofMultihash? hash
        return { peer with textForm := .cid text }
    | _ => throw .invalidCid

/-- The newtype exposes its checked invariant without a repeated runtime test. -/
theorem valid_multihash (peer : PeerId) : Valid peer.multihash := peer.valid

end PeerId

end Libp2p.Identity
