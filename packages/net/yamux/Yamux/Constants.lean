/-!
# The constants of `net/yamux`

Each fact has one home (ARCHITECTURE §3.8; PRINCIPLES 1.5). Every other
module of the package imports this one. The numbers come from the yamux
spec (`vendor/specs/yamux/README.md`) where the spec fixes them, and
from go-yamux v5.1.0 (`vendor/go-yamux`) where the spec is silent;
each docstring says which.
-/

set_option autoImplicit false

namespace Yamux

/-- The size of a frame header: version (8 bits), type (8 bits), flags
(16 bits), stream id (32 bits), and length (32 bits), "a 12 byte
overhead" in the spec. -/
def headerSize : Nat := 12

/-- The one protocol version the spec defines: "At the current time,
the field is always set to 0". -/
def version : Nat := 0

/-- The receive window of a new stream, 256 KiB ("Flow Control"). Both
sides assume it at the start. We never grant more, so this number also
caps the bytes that one stream buffers, and the declared length of any
data frame we accept (ARCHITECTURE §5.1). -/
def initialWindow : Nat := 256 * 1024

/-- The point at which a window update goes out: the application has
consumed half the window. A smaller update would cost a frame per read.
go-yamux uses the same half-window rule (`vendor/go-yamux/util.go`,
lines 103 to 107). -/
def windowUpdateThreshold : Nat := initialWindow / 2

/-- The largest data frame we send, 64 KiB: the frame-length cap of the
send side. A larger write goes out as several frames, so one stream
cannot hold the connection for a whole window. go-yamux sends at most
its `MaxMessageSize`, 64 KiB by default (`vendor/go-yamux/mux.go`,
line 82). The receive side needs no
second cap: `initialWindow` bounds every data frame we accept. -/
def maxDataFrame : Nat := 64 * 1024

/-- The control frames that may wait for the writer: the echo of a
ping, and the ACK or RST that answers a SYN. The peer causes each one.
Beyond the cap the session drops the ping echoes, and holds back new
events until the SYN answers have gone (ARCHITECTURE §4.8). The spike
set the cap at 1024. -/
def controlQueueCap : Nat := 1024

/-- The ACK backlog: "at most allow an ACK backlog of 256 streams"
("Implementation considerations"). It bounds our own streams that wait
for the peer's ACK, and the inbound streams that wait for
`acceptStream`. -/
def backlogCap : Nat := 256

/-- The inbound streams that may be live at once, accepted or not: 256.
The package ARCHITECTURE caps "all unrequested streams, accepted or
not", which is stricter than the spec's ACK backlog of 256
("Decisions"). Past it the core resets the new stream. The cap bounds
the session map together with the retirement rule (root §4.8). -/
def maxIncomingStreams : Nat := 256

/-- The chunks that a stream's inbox holds for the reader: the bound of
the per-stream `Chan` of ARCHITECTURE §3.3. Bytes that arrive while it
is full wait in the stream's state, joined into one chunk, and the
window bounds them. The inbox has one slot more, for the reset or the
end of the session, so that mark always fits. The spec fixes no buffer
layout. The number follows go-yamux, whose receive buffer allocates 16
segments up front, one per frame (`newSegmentedBuffer`,
`vendor/go-yamux/util.go`, line 83). Past them, go grows the buffer, and the core joins
the bytes instead. -/
def inboxChunks : Nat := 16

/-- The events that wait for the loop: the operations of the
application, and at most one read of the reader, which holds one
credit (`Yamux/Loop.lean`, "The reader's credit"). A full queue parks
the poster (ARCHITECTURE §3.3). The spec fixes no number. It follows
go-yamux, whose application writes park on a send queue of 64
(`sendCh`, `vendor/go-yamux/session.go`, line 144; the park is
`sendMsg`, line 536). -/
def eventQueueCap : Nat := 64

/-- The time one write to the connection may take, 10 seconds. A peer
that stops reading parks the writer, and the loop waits for the writer
under back-pressure. At the deadline the writer closes the connection,
and the session ends with a fault (ARCHITECTURE §5.4). The spec fixes
no timeout. The number follows go-yamux, whose `ConnectionWriteTimeout`
is 10 seconds and closes the session the same way
(`vendor/go-yamux/mux.go`, line 76; `session.go`, lines 581 to 587). -/
def writeDeadlineMs : Nat := 10000

/-- The time a pong may take to answer our ping, 10 seconds. The spec
fixes no timeout. go-yamux waits for the pong one
`ConnectionWriteTimeout` (`Ping`, `vendor/go-yamux/session.go`, lines
428 to 436), the
constant behind `writeDeadlineMs`, so the number is that one. -/
def pingDeadlineMs : Nat := writeDeadlineMs

/-- The keepalive interval of a session that the host gives no policy
of its own, 30 seconds: after that long with no bytes from the peer,
the session pings, and a ping that no pong answers in time ends the
session (`Yamux/Core.lean`, "Time"). The host owns the keepalive policy
(ARCHITECTURE, "Decisions"). go-yamux enables keepalives by default
with `KeepAliveInterval` of 30 seconds (`vendor/go-yamux/mux.go`, lines
73 and 74), and the Go node of the interop target keeps the default (package
ARCHITECTURE, "Checked against the implementations"). -/
def keepaliveIntervalMs : Nat := 30000

/-- The first stream id past the 32-bit field. Every valid id is below
it. -/
def streamIdLimit : Nat := 2 ^ 32

end Yamux
