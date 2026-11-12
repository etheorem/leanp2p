import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core.Error
import Libp2p.Core.Mux
import Libp2p.Core.Policy

/-!
# The secured transport seam

Most transports hand over a raw byte stream, a `Streams.Connection`,
and the upgrader secures it and muxes it (ARCHITECTURE §4.9; the
connections spec, `vendor/specs/connections/README.md`, "Upgrading
Connections"). QUIC does both itself. Its handshake is TLS 1.3, which
proves the peer's identity ("Peers authenticate each other using the
TLS handshake logic described in the libp2p TLS spec", the QUIC spec,
`vendor/specs/quic/README.md`, "Peer Authentication"). Its streams are
native (RFC 9000 §2). A QUIC connection arrives secured and muxed, so
the upgrader has no stage to run on it.

`SecuredTransport` is the seam for such a transport (§3.1). Its dial
answers a `SecuredSession`: the muxer session, the two peer ids the
handshake proved, and the addresses. The host keeps a list of these
beside its list of `Streams.Transport` values. It serves a
`SecuredSession` as it serves an upgraded connection, with the same
checkpoints, dedup, and stream handlers.

go-libp2p draws the same line: its `transport.Transport.Dial` answers a
`CapableConn`, which is secured and muxed
(`vendor/go-libp2p/core/transport/transport.go`, lines 29 and 61), and
its TCP transport runs the upgrader inside its own dial
(`vendor/go-libp2p/p2p/transport/tcp/tcp.go`, line 302).
Here the upgrader stays in the host, so the TCP path is unchanged, and
a transport that needs no upgrade fills this second seam.

## The admission

A listener asks its owner about each inbound connection before the
connection costs a handshake (`Admit`). The owner asks the gater's
`allowInbound` and the resource manager's `openConnection`, as the host
does for a TCP connection before its upgrade. The scope the owner
opens comes back with the session. The listener releases it for a
connection that never reaches its `accept`. go-libp2p asks its
resource manager at the
same point of a QUIC handshake (`vendor/go-libp2p/config/config.go`,
`ConnContext`).

## The values

The production value is QUIC, `Libp2p.Quic.transport`, with its test
value `Libp2p.Quic.fixedKeyTransport` (fixed keys, a fixed wall clock).
The sim value is `Libp2p.Negotiate.securedOver`. It runs the upgrade of
`libp2p/negotiate` inside the dial and the accept of any
`Streams.Transport`, as go-libp2p's TCP transport runs it. Over the sim
transport it gives every suite above this seam a secured transport with
no socket (PRINCIPLES 1.4).
-/

set_option autoImplicit false

namespace Libp2p.Core

open Conc Multiformats Libp2p.Identity

/-- A connection that its transport has secured and muxed. -/
structure SecuredSession where
  /-- The muxer session: the transport's own streams. Its `join` waits
  for the whole connection. -/
  session : MuxSession
  /-- The peer id of our identity key. -/
  localPeer : PeerId
  /-- The peer id the peer proved in the handshake. -/
  remotePeer : PeerId
  /-- The address of our end. -/
  localAddr : Multiaddr
  /-- The address of the peer's end. -/
  remoteAddr : Multiaddr

/-- The owner's admission of an inbound connection, by its local and
remote addresses (the module doc, "The admission"): the scope of the
connection, or `none` to refuse it before its handshake. -/
abbrev Admit := (localAddr remoteAddr : Multiaddr) → BaseIO (Option ConnectionScope)

/-- A source of the secured sessions that peers dial to one address. -/
structure SecuredListener where
  /-- The address the listener serves. -/
  addr : Multiaddr
  /-- The next session, once its handshake has proved the peer, with the
  scope its admission opened. After `close`, the sessions the listener
  still holds, then `none`; `close` wakes a parked accept. The caller
  owns each session it takes, and its scope. -/
  accept : Async (Option (SecuredSession × ConnectionScope))
  /-- Stop the listener. A parked `accept` wakes, with a session the
  listener still holds or with `none`. The sessions it gave stay open
  until their owners close them. -/
  close : IO Unit
  /-- Wait until every task of the listener ends. The owner calls it
  after `close` and after the sessions the listener gave have ended
  (§3.1, "Lifecycle"; §4.1, rule 2). -/
  join : Async Unit

/-- The secured transport seam: which addresses it serves, how to reach
one, and how to serve one. -/
structure SecuredTransport where
  /-- True when this transport dials and listens on the address, from
  the shape of the address alone (as `Streams.Transport.handles`). -/
  handles : Multiaddr → Bool
  /-- Dial the address, and prove the peer. With an expected peer id,
  a peer that proves another id fails the dial with `authentication`
  (the TLS spec: "Clients MUST verify that the peer ID derived from the
  certificate matches the peer ID they intended to connect to"). The
  close of `abort` ends a dial that is still in its handshake, with
  `closed`. A host's shutdown closes its unauthenticated connections
  that way (§5.5), as it closes the pending connections of TCP. -/
  dial : Multiaddr → Option PeerId → (abort : Chan Unit) → ExceptT Error Async SecuredSession
  /-- Listen on the address, and admit each inbound connection through
  `admit` before its handshake. An address in use is a fault. -/
  listen : Multiaddr → (admit : Admit) → Async SecuredListener

end Libp2p.Core
