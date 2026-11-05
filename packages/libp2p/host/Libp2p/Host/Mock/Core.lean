import Conc
import Streams
import Libp2p.Host.Mock.Identity

/-!
# Mock: the surface of `libp2p/core` that the host uses

W5.2 (`libp2p/core`) has not merged, so the host builds against a mock
of its frozen surface (RULES.md, "Working ahead of the tree"). The
types are copies: the seam shapes of the core ARCHITECTURE, "Public
surface", with `MuxSession.openStream` carrying a `ProtocolId` (the mux
ARCHITECTURE, "Public surface"). The mock imports nothing from the real
package, and it states no axiom.

## The policy shapes

The core ARCHITECTURE fixes the three policy hooks and no signatures:
"the decision inputs beyond these are the seam's to refine as the host
lands (W5.6)". This unit fixes them, and the core ARCHITECTURE records
them. The peer of an inbound connection is unknown until the handshake
ends, so the gater and the resource manager each take a second decision
there, with the proved peer, as go-libp2p does:
`ConnectionGater.InterceptSecured` (`vendor/go-libp2p/core/connmgr/gater.go`)
and `ResourceScope.SetPeer` (`vendor/go-libp2p/core/network/rcmgr.go`).
The ranker answers a dial schedule, an address and a delay each, the
shape of go-libp2p's `AddrDelay` and `DialRanker`
(`vendor/go-libp2p/core/network/network.go`, lines 212 and 218).

A policy answer runs in `BaseIO`: it has no fault channel, so a policy
throw cannot lose a dial.

At the integration, the host imports `Libp2p.Core`, and the module goes.
-/

set_option autoImplicit false

namespace Libp2p.Host.Mock.Core

open Conc Streams Multiformats Libp2p.Host.Mock.Identity

/-- A protocol id, wrapped (§3.4). -/
structure ProtocolId where
  /-- The id text. -/
  toString : String
  deriving DecidableEq, Hashable, Ord, Repr

instance : ToString ProtocolId := ⟨ProtocolId.toString⟩

/-- The coarse error every seam returns (§4.9). Each arm carries the
rendered error of the implementation. -/
inductive Error where
  | protocol (detail : String)
  | authentication (detail : String)
  | timeout (detail : String)
  | closed (detail : String)
  deriving DecidableEq, Repr

/-- The log line of the error: the kind, then the rendered detail. -/
def Error.render : Error → String
  | .protocol d => s!"protocol error: {d}"
  | .authentication d => s!"authentication failure: {d}"
  | .timeout d => s!"timeout: {d}"
  | .closed d => s!"closed: {d}"

instance : ToString Error := ⟨Error.render⟩

/-- Our side of a connection (§4.9). -/
inductive Role where
  | initiator
  | responder
  deriving DecidableEq, Repr

/-- The connection after the handshake: the secure connection, the two
peer ids, the bytes the handshake read past its end, and the
completion of its tasks. -/
structure SecureConn extends Connection where
  /-- Our peer id. -/
  localPeer : PeerId
  /-- The peer id the handshake proved. -/
  remotePeer : PeerId
  /-- The bytes the handshake read past its end (§4.7). -/
  leftover : ByteArray
  /-- Wait until the secure connection's tasks end. -/
  join : ExceptT Error Async Unit

/-- The security seam. -/
structure SecurityProtocol where
  /-- The negotiated id. -/
  id : ProtocolId
  /-- Run the handshake over a connection, with the negotiation's
  leftover. -/
  handshake : Role → Connection → ByteArray → ExceptT Error Async SecureConn

/-- A muxer session. -/
structure MuxSession where
  /-- Open a stream, labeled with its protocol id. -/
  openStream : ProtocolId → ExceptT Error Async Stream
  /-- The next stream the peer opened; `none` once the session ends. -/
  accept : Async (Option Stream)
  /-- End the session. -/
  close : IO Unit
  /-- Wait until the session loop ends. -/
  join : ExceptT Error Async Unit

/-- The muxer seam. -/
structure Muxer where
  /-- The negotiated id. -/
  id : ProtocolId
  /-- Open a session over a secure connection, with the negotiation's
  leftover. -/
  «open» : Role → Connection → ByteArray → ExceptT Error Async MuxSession

/-- The callback a served stream reaches. -/
structure StreamHandler where
  /-- The id the handler serves. -/
  id : ProtocolId
  /-- Serve one stream. -/
  handle : Stream → ExceptT Error Async Unit

/-! ## The policy hooks (module doc, "The policy shapes") -/

/-- The connection gater. `true` allows. -/
structure ConnectionGater where
  /-- Before an outbound dial, by the expected peer and the address. -/
  allowDial : Option PeerId → Multiaddr → BaseIO Bool
  /-- After an accept, before any byte moves, by the two addresses. -/
  allowInbound : (localAddr remoteAddr : Multiaddr) → BaseIO Bool
  /-- After the handshake, before the muxer stage, by the proved peer. -/
  allowSecured : Role → PeerId → (localAddr remoteAddr : Multiaddr) → BaseIO Bool

/-- An admitted share of a limit. A second `release` does nothing. -/
structure Reservation where
  /-- Return the share. -/
  release : BaseIO Unit

/-- The resource scope of one admitted connection. -/
structure ConnectionScope where
  /-- Name the proved peer; `false` when the connection does not fit
  that peer's limits. -/
  setPeer : PeerId → BaseIO Bool
  /-- Admit one more stream; `none` when it does not fit. -/
  reserveStream : BaseIO (Option Reservation)
  /-- Admit this many more buffered bytes; `none` when they do not fit. -/
  reserveMemory : Nat → BaseIO (Option Reservation)
  /-- Return the connection's share and every share it still holds. -/
  release : BaseIO Unit

/-- The resource manager. -/
structure ResourceManager where
  /-- Admit a new connection, by its direction, the expected peer, and
  the remote address; `none` when it does not fit. -/
  openConnection : Role → Option PeerId → Multiaddr → BaseIO (Option ConnectionScope)

/-- One address of a dial schedule, with its delay from the start of
the dial, in milliseconds. -/
structure AddrDelay where
  /-- The address to dial. -/
  addr : Multiaddr
  /-- The wait before this dial. -/
  delayMs : Nat
  deriving DecidableEq, Repr

/-- The address ranker: the dial schedule of a peer's addresses. -/
structure AddressRanker where
  /-- The schedule, in dial order. -/
  rank : List Multiaddr → List AddrDelay

end Libp2p.Host.Mock.Core
