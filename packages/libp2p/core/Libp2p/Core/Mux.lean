import Conc
import Streams
import Libp2p.Core.ProtocolId
import Libp2p.Core.Error
import Libp2p.Core.Role

/-!
# The muxer seam

A muxer runs many streams over one secure connection (ARCHITECTURE
§4.9; the connections spec, "Stream Multiplexing"). The upgrader
negotiates it with multistream-select after the handshake and opens a
session over the `SecureConn`, through `SecureConn.toConnection`.

`Muxer` is the seam (§3.1), and `MuxSession` is the uniform view of
one running session. yamux fills the seam in `libp2p/mux`, over the
session of `net/yamux`; mplex follows in the same package. The muxer
session is a pure core and one loop task (§3.3). This view talks to
the loop and holds no state of its own (owned contract 5).

The spike split the seam into a client entry and a server entry. Here
one `open` field takes a `Role`, the shape of
`SecurityProtocol.handshake`, and each implementation derives its
stream-id parity from the role (the core pair, decisions).
-/

set_option autoImplicit false

namespace Libp2p.Core

open Conc Streams

/-- One running muxer session. -/
structure MuxSession where
  /-- Open a new outbound stream. The id is the protocol the caller
  will negotiate on the stream: mplex writes it into its NewStream
  frame as a label, and yamux drops it, since its SYN frame has no
  field for it (the mux pair, decisions). `.error` when the session
  refuses the stream or has ended. -/
  openStream : ProtocolId → ExceptT Error Async Stream
  /-- The next stream the peer opened. `none` once the session has
  ended: `close` wakes a parked accept, as `Listener.accept` does. -/
  accept : Async (Option Stream)
  /-- Shut the session down. Every parked `accept` wakes with `none`,
  and the session closes its connection. A second close does
  nothing. -/
  close : IO Unit
  /-- Wait until the session loop has ended, and answer how it ended:
  `.ok` for an orderly end, the protocol error otherwise (§3.5). The
  owner calls it after `close` (§3.1, "Lifecycle"; §4.1, rule 2). -/
  join : ExceptT Error Async Unit

/-- The muxer seam: one stream muxer that multistream-select can
negotiate. -/
structure Muxer where
  /-- The id that multistream-select negotiates, such as
  `/yamux/1.0.0`. -/
  id : ProtocolId
  /-- Start a session in the given role over the connection. The
  `ByteArray` holds the bytes the muxer negotiation over-read; the
  session loop takes them as its first input (§4.7). The
  implementation maps its own error into `Error` here, once (owned
  contract 6). -/
  -- `open` is a Lean keyword, so the declaration quotes the name in
  -- `«…»`. The field is still named `open`.
  «open» : Role → Connection → ByteArray → ExceptT Error Async MuxSession

end Libp2p.Core
