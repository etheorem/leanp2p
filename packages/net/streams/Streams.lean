import Streams.Constants
import Streams.Error
import Streams.Conn
import Streams.BufReader
import Streams.Framing
import Streams.Stream
import Streams.Sim
import Streams.Tcp

/-!
# Streams

Connections, buffered readers, and framing (ARCHITECTURE §4.7): the
`Transport` seam with the sim and TCP as its two values, the
`BufReader` and `Framing` reads, and the `Stream` seam over a muxer
loop. The package docs are under `docs/` beside this file.

The mocks under `Streams/Mock/` take the place of `base/bytes`,
`codec/varint`, and `codec/multiformats` until those units merge. The
root has no import line for them. The modules that need them import
them.
-/
