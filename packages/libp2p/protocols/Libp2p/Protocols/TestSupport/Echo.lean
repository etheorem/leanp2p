import Streams.Stream
import Libp2p.Core
import Libp2p.Protocols.StreamError

/-!
# Demo echo support

`/demo/echo/1.0.0` is the demo's echo protocol. The spike handler in
`Tests/Node.lean` reads one chunk, writes those bytes, and half-closes.
An initial EOF is an orderly end: the handler half-closes and returns.

This module holds that handler and the matching client. The client
writes one payload and reads one reply. The demo chooses the payload
and prints the result. This module does neither.

One chunk is the whole exchange. A later chunk stays on the stream.
The caller owns the stream. `serve` half-closes the write direction
on an orderly read. `exchange` leaves the stream open. A `Streams.Error`
maps through `mapStreamError`. A thrown `IO.Error` stays thrown.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.TestSupport.Echo

/-- The demo echo protocol id. -/
def protocolId : Libp2p.Core.ProtocolId :=
  { toString := "/demo/echo/1.0.0" }

/-- Read one chunk, write those bytes, and half-close. An initial EOF
half-closes and returns `.ok`. A stream error maps through
`mapStreamError`, and the call does not half-close. A thrown
`IO.Error` from the read, the write, or the half-close stays thrown.
The caller owns `s`. -/
def serve (s : Streams.Stream) : Conc.Async (Except Libp2p.Core.Error Unit) := do
  match ← s.read with
  | .error e => return .error (mapStreamError e)
  | .ok none =>
    s.close
    return .ok ()
  | .ok (some bytes) =>
    match ← s.write bytes with
    | .error e => return .error (mapStreamError e)
    | .ok () =>
      s.close
      return .ok ()

/-- The handler value. `id` is `protocolId`. `handle` ignores the
context and runs `serve`. -/
def handler : Libp2p.Core.StreamHandler where
  id := protocolId
  handle _ s := ExceptT.mk (serve s)

/-- Write `payload` and read one reply. `.ok none` is EOF before a
reply. A stream error maps through `mapStreamError`. A thrown
`IO.Error` stays thrown. The caller owns `s` and closes it. -/
def exchange (s : Streams.Stream) (payload : ByteArray) :
    Conc.Async (Except Libp2p.Core.Error (Option ByteArray)) := do
  match ← s.write payload with
  | .error e => return .error (mapStreamError e)
  | .ok () =>
    match ← s.read with
    | .error e => return .error (mapStreamError e)
    | .ok reply => return .ok reply

end Libp2p.Protocols.TestSupport.Echo
