import Streams
import Libp2p.Identity
import Libp2p.Core.Role

/-!
# The policy seams

Three hooks let a host apply policy without editing the host
(ARCHITECTURE §3.1, §4.9):

* the connection gater allows or denies an outbound dial, an inbound
  connection, and a connection once its handshake has proved the peer;
* the resource manager admits a connection or a stream when it fits
  the limits, and the limits of §9 (delta 4) are the stream count, the
  buffered bytes, and a memory ceiling, per peer and per connection;
* the address ranker turns the addresses of a peer into a dial
  schedule: an order, and a delay before each dial.

The root docs fix the three hooks and no signatures. The host pair
(W5.6) fixes the shapes, and the core pair records them ("The policy
shapes"). The peer id of an inbound connection is unknown until the
handshake ends, so the gater and the resource manager each take a
second decision there, with the proved peer id, as go-libp2p does:
`ConnectionGater.InterceptSecured(dir, peer, addrs)`
(`vendor/go-libp2p/core/connmgr/gater.go`) and
`ResourceScope.SetPeer(peer)` on the connection scope
(`vendor/go-libp2p/core/network/rcmgr.go`).

The host pair owns the default values and the test doubles (the core
pair, "Test values").

A policy answer runs in `BaseIO`: it reads its state and answers, and
it has no fault channel, so a policy throw cannot lose a dial. A
policy value keeps its counters behind its fields, in an `OnceRef`
that the fields close over, and exposes no cell (§3.1, owned
contract 5).

`Multiaddr` is the address type of `Connection`, and it reaches this
module through `Streams` (the core pair, "What the package must not
depend on").
-/

set_option autoImplicit false

namespace Libp2p.Core

open Multiformats Libp2p.Identity

/-- The connection gater: allow or deny a connection at three
checkpoints. `true` allows. -/
structure ConnectionGater where
  /-- Before an outbound dial: allow a dial to the address. The peer id
  is the one the dial expects, `none` when the caller dials an address
  alone. -/
  allowDial : Option PeerId → Multiaddr → BaseIO Bool
  /-- After an accept, before any byte moves: allow the inbound
  connection, by the addresses of the accepted `Connection`. -/
  allowInbound : (localAddr remoteAddr : Multiaddr) → BaseIO Bool
  /-- After the handshake, before the muxer stage: allow the
  connection, now that the handshake has proved the peer id. This is
  the first checkpoint that can deny an inbound connection by its
  peer. -/
  allowSecured : Role → PeerId → (localAddr remoteAddr : Multiaddr) → BaseIO Bool

/-- An admitted share of a limit. The holder calls `release` when the
connection, the stream, or the buffer is gone, and the share returns
to the limit. A second release does nothing. -/
structure Reservation where
  /-- Return the share to the limit. -/
  release : BaseIO Unit

/-- The resource scope of one admitted connection. The per-connection
limits apply from the start. The per-peer limits apply once `setPeer`
names the peer, and from then on every reservation of the scope counts
against that peer too. -/
structure ConnectionScope where
  /-- Name the peer that the handshake proved. `true` attaches the
  peer, and the connection counts against that peer's limits from now
  on. `false` when the connection does not fit the limits of that
  peer. A `false` attaches nothing, and the caller then closes the
  connection and releases the scope, which returns the
  per-connection share only. A scope takes one peer: every call after
  the first answer of `true` answers `false` and changes nothing. -/
  setPeer : PeerId → BaseIO Bool
  /-- Admit one more stream on the connection. `none` when the stream
  does not fit the limits. -/
  reserveStream : BaseIO (Option Reservation)
  /-- Admit this many more buffered bytes on the connection. `none`
  when they do not fit the limits. -/
  reserveMemory : Nat → BaseIO (Option Reservation)
  /-- Return the connection's share, and every share it still holds,
  to the limits. A second release does nothing. -/
  release : BaseIO Unit

/-- The resource manager: admit a connection when it fits the
limits. -/
structure ResourceManager where
  /-- Admit a new connection, by its direction, the peer a dial
  expects, and its remote address. The peer id is `none` on an
  accept, or on a dial of an address alone. A manager can count an
  expected peer against that peer's limits here, so concurrent dials
  to one peer stop before their handshakes run. rust-libp2p's
  `handle_pending_outbound_connection` takes `maybe_peer` for the same
  reason (`swarm/src/behaviour.rs` in libp2p/rust-libp2p). The
  expected id is unproved; `ConnectionScope.setPeer` names the proved
  peer after the handshake. `none` when the connection does not fit
  the limits. -/
  openConnection : Role → Option PeerId → Multiaddr → BaseIO (Option ConnectionScope)

/-- One address in a dial schedule: dial `addr` once `delayMs`
milliseconds have passed since the dial began. The unit is the one of
`Conc.Clock`. go-libp2p's `AddrDelay` has the same two fields
(`vendor/go-libp2p/core/network/network.go`, line 212). -/
structure AddrDelay where
  /-- The address to dial. -/
  addr : Multiaddr
  /-- The wait before this dial, in milliseconds from the start of the
  dial. -/
  delayMs : Nat
  deriving DecidableEq, Repr

/-- The address ranker: the dial schedule for the addresses of a peer,
in dial order. It is a pure function of the addresses, as go-libp2p's
`DialRanker` is (`vendor/go-libp2p/core/network/network.go`, line
218). With every delay 0 it is a plain order. -/
structure AddressRanker where
  /-- The schedule: each address with its dial delay. -/
  rank : List Multiaddr → List AddrDelay

end Libp2p.Core
