import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core.ProtocolId
import Libp2p.Core.Error

/-!
# The stream handler seam

When the peer opens a stream, it proposes a protocol id with
multistream-select, and the host answers with the handler registered
under that id (the connections spec, "Protocol Negotiation"). The host
keys its registry by the id, `Std.HashMap ProtocolId StreamHandler`
(ARCHITECTURE §3.10), and hands the negotiated stream to the callback.
The stream already carries the bytes the stream negotiation read past
its last message (`Stream.prependBytes`, §4.7).

The callback also gets the `StreamContext` of the connection: the peer
id the handshake proved and the peer's transport address. One handler
serves every peer, so a protocol that acts per peer reads the peer
here. Identify push keys the peerstore on it, and the identify
responder reports the address as the observed address. go-libp2p reads
the same two facts from `s.Conn()` (`RemotePeer`, `RemoteMultiaddr`;
`vendor/go-libp2p/p2p/protocol/identify/id.go`).

A protocol package builds its handler value with the id constant of
its own module (§3.4). A handler failure closes the stream and leaves
the session open; the host makes that call (the host pair, public
surface).
-/

set_option autoImplicit false

namespace Libp2p.Core

open Conc Streams Libp2p.Identity

/-- What the host knows about the connection under a served stream. -/
structure StreamContext where
  /-- The peer id the security handshake proved. -/
  remotePeer : PeerId
  /-- The peer's transport address, as the connection reports it. -/
  remoteAddr : Multiformats.Multiaddr

/-- The handler of one protocol: the id the host registers it under,
and the callback that serves a negotiated stream. -/
structure StreamHandler where
  /-- The protocol id the host matches proposals against. -/
  id : ProtocolId
  /-- Serve one stream of the connection that `StreamContext`
  describes. `.error` reports a protocol failure on this stream to the
  host. -/
  handle : StreamContext → Stream → ExceptT Error Async Unit

end Libp2p.Core
