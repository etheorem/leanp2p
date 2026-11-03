import Conc

/-!
# Streams mocks for unit 1b

The streams seam types live in `net/streams` (#32, not merged yet).
This module holds `Connection`, `BufReader`, and `Stream` verbatim from
the streams ARCHITECTURE "Public surface", and the one constant the
upgrader wires, so the upgrader compiles against the frozen shapes.
The imports swap to `Streams` when the streams package lands.

`Connection` omits `localAddr` and `remoteAddr`. The upgrader never
reads an address, and a `Multiaddr` import would break the package's
own import list (negotiate ARCHITECTURE, "What the package must not
depend on"). `BufReader.readExactly` stays undeclared: the core owns
framing, and this package reads raw chunks (negotiate ARCHITECTURE,
"From the net group").
-/

set_option autoImplicit false

namespace Libp2p.Negotiate.Mock.Streams

/-- A byte stream. The fields are exactly `Conc.Pipe`'s methods, so
the test pair needs no adapter (`Pipe.lean:33,41,46`). `read` returns
`none` on the end of the stream. -/
structure Connection where
  read : Conc.Async (Option ByteArray)
  write : ByteArray → Conc.Async (Except Conc.Error Unit)
  close : BaseIO Unit

/-- One stage's reader (streams ARCHITECTURE, "No reader strand").
Two stages never share one reader. -/
structure BufReader where
  read : Conc.Async (Option ByteArray)

/-- The reader of one connection. Each upgrade stage builds its own
reader over the connection of that stage. -/
def BufReader.ofConn (c : Connection) : BufReader := ⟨c.read⟩

/-- The application view over a muxer loop. The upgrader never calls
these fields; they type the `MuxSession` surface of the core mock. -/
structure Stream where
  read : Conc.Async (Option ByteArray)
  write : ByteArray → Conc.Async (Except Conc.Error Unit)
  close : IO Unit
  reset : IO Unit

/-- The 30 s upgrade deadline (root §5.4). The real home is
`Streams/Constants.lean`; this mock moves there when the streams
package lands (negotiate ARCHITECTURE, "Decisions"). -/
def upgradeDeadlineMs : Nat := 30000

end Libp2p.Negotiate.Mock.Streams
