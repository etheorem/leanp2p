/-!
# The constants of `net/streams`

Each fact has one home (ARCHITECTURE §3.8; PRINCIPLES 1.5). This module
holds the constants that the package owns. The framing caps of §5.1
belong to the protocol layers that read the frames. Each layer passes
its cap to `Framing.read` from its own constants module, so this module
names none of them.
-/

set_option autoImplicit false

namespace Streams

/-- The deadline of an unauthenticated phase, in milliseconds: the 30 s
of ARCHITECTURE §5.4. A silent peer that sends nothing during the dial
or the handshake fails at this deadline, so no task parks forever on
it. -/
def unauthDeadlineMs : Nat := 30000

/-- The chunks in flight on one direction of a sim connection. A writer
parks while the pipe holds this many unread chunks, so the sim carries
back-pressure as a TCP window does. -/
def simPipeChunks : Nat := 64

/-- The dials that a sim listener queues before its owner accepts them.
A dial parks while the queue is full, as a TCP backlog makes a connect
wait. -/
def simBacklog : Nat := 16

end Streams
