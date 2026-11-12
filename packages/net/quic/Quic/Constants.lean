import Streams

/-!
# The constants of `net/quic`

Each fact has one home (root ARCHITECTURE §3.8; PRINCIPLES 1.5). This
module holds every number of the package. The shim takes the transport
parameters, the windows, and the timeouts from here at the start of an
endpoint (`QuicNative.endpointNew`), so C holds none of them.

The numbers follow the QUIC configuration of the go reference, the
peer of the interop check, and quic-go v0.62.0 under it where that
configuration keeps quic-go's default. The package ARCHITECTURE, "The
parameters", names the file and the line of each.
-/

set_option autoImplicit false

namespace Quic

/-- The bidirectional streams the peer may open at once: 256, the go
reference's `MaxIncomingStreams`. -/
def maxStreamsBidi : Nat := 256

/-- The receive window a stream starts with: 512 KiB, quic-go's
`DefaultInitialMaxStreamData` (`internal/protocol/params.go`, line 19).
ngtcp2 grows the window while the reader keeps up, to
`streamWindowMax`. -/
def streamWindow : Nat := 512 * 1024

/-- The largest receive window of a stream: 10 MiB, the go reference's
`MaxStreamReceiveWindow`. -/
def streamWindowMax : Nat := 10 * 1024 * 1024

/-- The receive window a connection starts with: 768 KiB, quic-go's
`DefaultInitialMaxData`, 1.5 times the stream window
(`ConnectionFlowControlMultiplier`, `internal/protocol/params.go`, lines
16 and 22). -/
def connWindow : Nat := 3 * streamWindow / 2

/-- The largest receive window of a connection: 15 MiB, the go
reference's `MaxConnectionReceiveWindow`. It bounds the bytes one peer
can make us hold: the inboxes of all its streams together (root
§5.1). -/
def connWindowMax : Nat := 15 * 1024 * 1024

/-- The idle timeout: 30 s, quic-go's `DefaultIdleTimeout`
(`internal/protocol/params.go`, line 94). -/
def idleTimeoutMs : Nat := 30000

/-- The keep-alive period: 15 s, the go reference's `KeepAlivePeriod`.
Half the idle timeout, so a live peer never idles out. -/
def keepAliveMs : Nat := 15000

/-- The deadline of the handshake: the unauthenticated deadline of root
§5.4, whose one home is `Streams.unauthDeadlineMs`. ngtcp2 counts it
from the connection's start (`ngtcp2_settings.handshake_timeout`). -/
def handshakeTimeoutMs : Nat := Streams.unauthDeadlineMs

/-- The largest datagram a read takes: 65527 bytes. A QUIC endpoint
must take datagrams up to the `max_udp_payload_size` it announces
(RFC 9000 §18.2), and the shim announces ngtcp2's default, the RFC's
default, 65527 (`NGTCP2_DEFAULT_MAX_RECV_UDP_PAYLOAD_SIZE`). -/
def maxDatagram : Nat := 65527

/-- The bytes of a stream that the peer has not acknowledged, past which
a write parks: 1 MiB. The shim keeps every unacknowledged byte, since
QUIC may send it again (RFC 9000 §13.3), so this cap bounds the memory
one stream holds on our side (root §5.1). No reference sets such a
number: quic-go's `Write` returns once all but a small tail of the
bytes have gone into frames (`send_stream.go`, `write`),
and the stream sends only as far as the peer's window allows. This one
is ours. -/
def streamSendCap : Nat := 1024 * 1024

/-- The datagrams that wait for the endpoint's loop: 1024, quic-go's
`MaxServerUnprocessedPackets` (`internal/protocol/params.go`, line 40).
A full queue parks the reader (root §3.3), and a parked reader leaves
the datagrams in the socket's buffer, where the kernel drops the excess
and QUIC's loss recovery sends them again. -/
def datagramQueueCap : Nat := 1024

/-- The streams that may wait for `accept` on one connection: as many
as the peer may open. A full queue cannot occur: a stream of the peer's
gives its credit back only once it is over and accepted
(`Quic/Loop.lean`, "A new connection"), so the peer never has more streams
open or waiting. -/
def acceptBacklog : Nat := maxStreamsBidi

/-- The connections that may wait for `accept` on one listener: 32,
quic-go's `MaxAcceptQueueSize` (`internal/protocol/params.go`, line 54).
A connection that finds the queue full closes with
`connectionRefused`, as quic-go's server closes it (`server.go`,
`handleNewConn`). -/
def listenBacklog : Nat := 32

/-- The server connections of one endpoint that may be in their
handshake at once. Each costs an ngtcp2 connection and a TLS session
until its handshake ends or its deadline passes. The peer has proved
nothing by then, so the count bounds what unauthenticated datagrams
can make us hold (root §5.1). A client past the count gets
CONNECTION_REFUSED with no state kept. quic-go keeps no such count
(`server.go`, `handleInitialImpl`). The go reference counts these
connections in its resource manager's transient scope, which holds an
inbound connection until its peer is known. The scope admits 32 inbound
connections on a minimal node, with no scaling by memory (the package
ARCHITECTURE, "The parameters", names the file and the lines). The
host's resource manager limits nothing yet (root §9, delta 4), so the
endpoint keeps that count itself. -/
def maxHandshakes : Nat := 32

/-- The connections in their handshake from which a new client must
prove its address with a Retry first (RFC 9000 §8.1.2): half of
`maxHandshakes`. A spoofed source never receives the Retry. So spoofed
Initials can fill this half at most, and the clients that answer the
Retry keep the other half. The go reference makes the same split. Its
limiter "allows maxAllowedConns / 2 unverified addresses to begin
handshake", and the package ARCHITECTURE ("Flow control and the
bounds") names the file. -/
def retryThreshold : Nat := maxHandshakes / 2

/-- The closing periods a listening endpoint keeps at once: 64, twice
`maxHandshakes`. A listener's close refuses every connection in its
handshake, and the count leaves room for the closes of as many other
connections. Past the count the oldest record goes, which RFC 9000
§10.2 allows. The endpoint sends no stateless reset, so a late packet
of that connection draws no answer. The peer then ends the connection
by its idle timer. quic-go keeps a record for every closed connection
with no count, and no spec or reference gives one. This one is ours. -/
def maxClosingPeriods : Nat := 2 * maxHandshakes

/-- The transport error CONNECTION_REFUSED, 0x2 (RFC 9000 §20.1): "The
server refused to accept a new connection". A listener closes these
connections with it:

* a connection that its accept queue cannot take;
* the connections still in their handshake when the listener closes;
* a client past `maxHandshakes`;
* a client that its caller's admission refuses. -/
def connectionRefused : UInt64 := 0x2

/-- The transport error INVALID_TOKEN, 0xb (RFC 9000 §20.1): "the
server SHOULD immediately close ... with an INVALID_TOKEN error" when
an Initial carries a Retry token that fails the check (§8.1.2). -/
def invalidToken : UInt64 := 0xb

/-- The application error code of an orderly close. RFC 9000 §20.2
leaves the space to the application, and the go reference's `Close`
sends 0 (the package ARCHITECTURE, "The parameters"). -/
def orderlyClose : UInt64 := 0

/-- The application error code of a stream reset (RESET_STREAM and
STOP_SENDING, RFC 9000 §3.5): 0, the go reference's `reset` constant,
which its `Reset` sends in both directions (the package ARCHITECTURE,
"The parameters"). -/
def streamResetCode : UInt64 := 0

end Quic
