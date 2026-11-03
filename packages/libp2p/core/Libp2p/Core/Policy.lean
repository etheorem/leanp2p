import Libp2p.Core.Security
import Libp2p.Core.Mock.Identity
import Libp2p.Core.Mock.Multiformats

/-!
# Host policy interfaces

Connection admission, resource accounting, and address ordering
(ARCHITECTURE §4.9).

The gater and resource manager use `BaseIO` to consult mutable policy
state without parking. A policy that cannot decide denies the request.
The address ranker is pure.
-/

set_option autoImplicit false

namespace Libp2p.Core

open Libp2p.Core.Mock

/-- Admission or reservation decision returned by a policy. -/
inductive Decision where
  /-- Permit the operation. -/
  | allow
  /-- Refuse the operation. -/
  | deny
  deriving DecidableEq, Repr, Hashable

/-! ## Connection gater -/

/-- Admission checks. On `deny`, the host refuses the dial or closes
the connection. -/
structure ConnectionGater where
  /-- Before the host dials the peer at the address. -/
  allowDial : Identity.PeerId → Multiformats.Multiaddr → BaseIO Decision
  /-- After the listener accepts a connection from the remote address,
  before any negotiation. The peer id is not known yet. -/
  allowAccept : Multiformats.Multiaddr → BaseIO Decision
  /-- After the security handshake: our role, and the peer id the
  remote side proved (`SecureConn.remotePeer`). An inbound connection
  meets its first peer-id check here. -/
  allowSecured : Role → Identity.PeerId → BaseIO Decision

/-! ## Resource manager -/

/-- Memory reservations for a connection or stream. A stream scope
also holds its stream slot. The owner closes the scope when done. -/
structure ResourceScope where
  /-- Ask for `n` more bytes of buffer memory. `deny` when the bytes
  would pass a limit; the caller then refuses the data, or tears down. -/
  reserveMemory : Nat → BaseIO Decision
  /-- Give back `n` bytes reserved before. -/
  releaseMemory : Nat → BaseIO Unit
  /-- Give back the slot and every byte the scope still holds. A second
  close does nothing. -/
  close : BaseIO Unit

/-- A connection grant whose streams share its peer and connection
limits. The owner closes all stream scopes before this scope. -/
structure ConnectionScope extends ResourceScope where
  /-- Associate `SecureConn.remotePeer` once, after the handshake and
  before starting the muxer. Existing reservations then count against
  the peer. On `deny`, the host closes the connection. -/
  setPeer : Identity.PeerId → BaseIO Decision
  /-- Grant a stream on this connection, or return `none` when a peer
  or connection limit would be exceeded. `initiator` opens locally;
  `responder` accepts a stream opened by the peer. -/
  openStream : Role → BaseIO (Option ResourceScope)

/-- Grants connections; each connection scope grants its own streams. -/
structure ResourceManager where
  /-- Grant a connection to the remote address, or return `none` when
  a limit would be exceeded. The scope learns the authenticated peer
  through `setPeer`. -/
  openConnection : Role → Multiformats.Multiaddr → BaseIO (Option ConnectionScope)

/-! ## Address ranker -/

/-- Reorder addresses for dialing, preserving their multiplicities.
The gater filters addresses through `allowDial`. -/
structure AddressRanker where
  /-- The addresses in dial order. -/
  rank : Identity.PeerId → List Multiformats.Multiaddr → List Multiformats.Multiaddr
  /-- Ranking preserves every address and its multiplicity. -/
  rank_perm : ∀ (peer : Identity.PeerId) (addrs : List Multiformats.Multiaddr),
    (rank peer addrs).Perm addrs

/-- Ranking preserves the number of entries, including duplicates. -/
theorem AddressRanker.length_rank (r : AddressRanker) (peer : Identity.PeerId)
    (addrs : List Multiformats.Multiaddr) : (r.rank peer addrs).length = addrs.length :=
  (r.rank_perm peer addrs).length_eq

/-- An address occurs in the ranked list exactly when it occurs in the input. -/
theorem AddressRanker.mem_rank (r : AddressRanker) (peer : Identity.PeerId)
    (addrs : List Multiformats.Multiaddr) (a : Multiformats.Multiaddr) :
    a ∈ r.rank peer addrs ↔ a ∈ addrs :=
  (r.rank_perm peer addrs).mem_iff

end Libp2p.Core
