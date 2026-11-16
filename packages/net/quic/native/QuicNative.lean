import TlsNative
import Std.Async.UDP

/-!
# The ngtcp2 bindings

The `@[extern]` declarations of `c/quic_shim.c`. One `Endpoint` holds
every QUIC connection of one UDP socket. The caller feeds it the
datagrams it reads, the commands of the application, and the timer
expiries. Each call carries the time in milliseconds of the caller's
clock. The caller then drains the two queues: the events (`nextEvent`)
and the datagrams to send (`nextPacket`). `Quic/Loop.lean` runs the
one loop that does this. No caller outside `net/quic` imports this
module.

**Addresses** cross as bytes: the family (4 or 6), the address in
network order, then the port, big-endian (`Quic/Address.lean`).

**Connections** are named by a handle that the endpoint gives and
never reuses. A command for a handle that names no connection does
nothing.

**The certificate check** is the caller's pure function,
`ByteArray → Option String`, as for `net/tls`: `none` accepts, and
`some reason` refuses. The shim attaches it to the connection's `SSL`
(`tls_shim.h`, `leanp2p_tls_attach_check`), and the context's verify
callback runs it inside the handshake. A dial passes it to `connect`.
A server connection gets its own when it starts. `recv` answers
`true` for a datagram that would open one. The caller then passes the
check to `accept` with that datagram, or refuses the connection with
`refuse`. So a caller can admit each connection, and build its check,
at the time its handshake starts.

**The bounds of new connections** are the shim's, from the numbers the
caller passes to `endpointNew`:

* the count of server connections in their handshake (`maxHandshakes`);
* the count past which a client proves its address with a Retry first
  (`retryThreshold`);
* the closing periods a listener keeps (`maxClosingPeriods`).

`recv` answers `true` only for a client within them. The shim answers
the others itself, with no state kept.

**Ownership.** The shim borrows every argument (`@&`). An endpoint
holds a reference to its `TlsNative.Context`, and each connection's
`SSL` holds one to its check. Every call runs in `IO`: the endpoint is
mutable state, and the handshake draws randomness.

**Threads.** The endpoint has no lock: one task, the endpoint's loop,
makes every call.
-/

set_option autoImplicit false

namespace QuicNative

/-- The carrier of an `Endpoint`. The standard pattern of an opaque FFI
type: a `NonemptyType` whose `type` field is the type. -/
opaque EndpointPointed : NonemptyType

/-- One QUIC endpoint: the connections of one UDP socket. -/
def Endpoint : Type := EndpointPointed.type

instance : Nonempty Endpoint := EndpointPointed.property

/-- One event, as C lays it out: the object field, then the scalars in
declaration order. `kind` is one of the numbers of `EventKind`. -/
structure EventRaw where
  data : ByteArray
  conn : UInt64
  stream : UInt64
  code : UInt64
  kind : UInt8

/-- The event kinds of the shim (`c/quic_shim.c`, the `EV_` enum). A
connection ends with exactly one of the last seven. -/
inductive EventKind where
  /-- The handshake is done. `data` holds the peer's certificate,
  DER, which the check accepted. -/
  | handshakeDone
  /-- The peer opened `stream`. -/
  | streamOpened
  /-- `data` arrived on `stream`; `code` is `dataFin` when the peer's
  FIN follows it. -/
  | streamData
  /-- The peer reset its sending part of `stream` (RESET_STREAM), so
  our reads end; `code` is the application error. -/
  | streamReset
  /-- The peer will read no more of `stream` (STOP_SENDING), so our
  writes end; `code` is the application error. -/
  | streamStopped
  /-- Both directions of `stream` are over. -/
  | streamClosed
  /-- The peer acknowledged bytes of `stream`; `code` is the count it
  has not acknowledged. -/
  | streamAcked
  /-- The peer allows more streams of ours. -/
  | openCredit
  /-- An application close, ours or the peer's, or the peer's
  transport close with NO_ERROR. `code` is the error, 0 for an orderly
  end, and `data` is the reason. -/
  | connClosed
  /-- Our TLS refused the peer's certificate inside the handshake;
  `data` is the reason, `code` the transport error we sent. -/
  | connRefused
  /-- We closed on a transport error: a library error, a TLS failure
  other than a refused certificate, no ALPN, or our own refusal with
  CONNECTION_REFUSED (a full accept queue, a listener's close). `code`
  is the error we sent. -/
  | connFailed
  /-- The peer closed on a transport error; `code` is its error. -/
  | peerFailed
  /-- The handshake did not finish within its deadline. -/
  | connTimeout
  /-- The idle timer ended the connection. -/
  | connIdle
  /-- The connection ended with no CONNECTION_CLOSE: a stateless reset
  of the peer, or a server drop. -/
  | connDropped
  deriving DecidableEq, Repr

/-- The number of each kind, as the shim writes it. -/
def EventKind.toCode : EventKind → UInt8
  | .handshakeDone => 1
  | .streamOpened => 2
  | .streamData => 3
  | .streamReset => 4
  | .streamStopped => 5
  | .streamClosed => 6
  | .streamAcked => 7
  | .openCredit => 8
  | .connClosed => 9
  | .connRefused => 10
  | .connFailed => 11
  | .peerFailed => 12
  | .connTimeout => 13
  | .connIdle => 14
  | .connDropped => 15

/-- The kind of a raw event number. -/
def EventKind.ofCode? : UInt8 → Option EventKind
  | 1 => some .handshakeDone
  | 2 => some .streamOpened
  | 3 => some .streamData
  | 4 => some .streamReset
  | 5 => some .streamStopped
  | 6 => some .streamClosed
  | 7 => some .streamAcked
  | 8 => some .openCredit
  | 9 => some .connClosed
  | 10 => some .connRefused
  | 11 => some .connFailed
  | 12 => some .peerFailed
  | 13 => some .connTimeout
  | 14 => some .connIdle
  | 15 => some .connDropped
  | _ => none

/-- The conformance of the table (root ARCHITECTURE §3.4): every kind
reads back from its number. -/
theorem EventKind.ofCode?_toCode (k : EventKind) : EventKind.ofCode? k.toCode = some k := by
  cases k <;> rfl

/-- The `code` of a `streamData` event whose bytes the peer's FIN
follows (`STREAM_DATA_FIN` of the shim). -/
def dataFin : UInt64 := 1

/-- The answer of `streamWrite` when the stream takes no bytes
(`WRITE_REFUSED` of the shim). -/
def writeRefused : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The answer of `openStream` when the peer allows no more streams
now (`OPEN_BLOCKED` of the shim). -/
def openBlocked : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The answer of `openStream` when the connection is gone or not set
up yet (`OPEN_GONE` of the shim). -/
def openGone : UInt64 := 0xFFFFFFFFFFFFFFFE

/-- The answer of `expiry` when no timer is set (`NO_EXPIRY` of the
shim). -/
def noExpiry : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- A new endpoint for the socket bound at `localAddr`, on the TLS
context `tls`. The numbers come from `Quic/Constants.lean`, each in
bytes or milliseconds:

* the streams the peer may open;
* the initial and the largest stream receive window, and the same for
  the connection;
* the idle timeout, the keep-alive period, and the handshake deadline;
* the bounds of new connections (the module doc);
* the transport errors CONNECTION_REFUSED and INVALID_TOKEN that the
  shim sends for those bounds.

`accept` lets the endpoint take new connections, as a listener does.
The answer is `none` when the address does not parse, when the crypto
glue did not start, or when the endpoint could not draw its random
secret. -/
@[extern "leanp2p_quic_endpoint_new"]
opaque endpointNew (tls : @& TlsNative.Context) (localAddr : @& ByteArray) (accept : Bool)
  (maxStreamsBidi streamWindow streamWindowMax connWindow connWindowMax : UInt64)
  (idleTimeoutMs keepAliveMs handshakeTimeoutMs : UInt64)
  (maxHandshakes retryThreshold maxClosingPeriods : UInt64)
  (connectionRefused invalidToken : UInt64) : IO (Option Endpoint)

/-- Bind a fresh UDP socket to `addr` (the shim's bytes) with no address
reuse, so no other socket shares its port. `Std.Async.UDP`'s own bind
always sets SO_REUSEADDR (the package ARCHITECTURE, "Decisions", the
exclusive bind). Call it once, before any receive or send on the
socket. A port another socket holds fails with EADDRINUSE. -/
@[extern "leanp2p_quic_udp_bind"]
opaque udpBind (socket : @& Std.Internal.UV.UDP.Socket) (addr : @& ByteArray) : IO Unit

/-- Dial `remote` at `now`, with the certificate check `check`: the
handle of the new connection, or 0. -/
@[extern "leanp2p_quic_connect"]
opaque connect (ep : @& Endpoint) (remote : @& ByteArray) (now : UInt64)
  (check : @& (ByteArray → Option String)) : IO UInt64

/-- Take one datagram from `src` at `now`. `true` when the datagram
would open a new connection within the bounds (the module doc); the
caller then calls `accept` or `refuse` with it. -/
@[extern "leanp2p_quic_recv"]
opaque recv (ep : @& Endpoint) (datagram : @& ByteArray) (src : @& ByteArray) (now : UInt64) :
  IO Bool

/-- Open the server connection of the datagram that `recv` answered
`true` for, with the certificate check `check`, and read the datagram
into it. The answer is the handle of the new connection, or 0 when
none opened. The read can end the connection at once, and its end
event then waits in the queue. -/
@[extern "leanp2p_quic_accept"]
opaque accept (ep : @& Endpoint) (datagram : @& ByteArray) (src : @& ByteArray) (now : UInt64)
  (check : @& (ByteArray → Option String)) : IO UInt64

/-- Refuse the new connection of the datagram that `recv` answered
`true` for: the client gets CONNECTION_REFUSED, and the endpoint keeps
no state for it. -/
@[extern "leanp2p_quic_refuse"]
opaque refuse (ep : @& Endpoint) (datagram : @& ByteArray) (src : @& ByteArray) (now : UInt64) :
  IO Unit

/-- Write the packets of every connection into the datagram queue, and
free the closed connections. -/
@[extern "leanp2p_quic_flush"]
opaque flush (ep : @& Endpoint) (now : UInt64) : IO Unit

/-- Run the timers due at `now`. -/
@[extern "leanp2p_quic_expire"]
opaque expire (ep : @& Endpoint) (now : UInt64) : IO Unit

/-- The earliest timer, in the caller's milliseconds; `noExpiry` when
none is set. -/
@[extern "leanp2p_quic_expiry"]
opaque expiry (ep : @& Endpoint) : IO UInt64

/-- Close a connection with the error `code` and a reason (RFC 9000
§10.2): an application error, or a transport error when `transport`
holds, as the endpoint's own refusal of a connection. -/
@[extern "leanp2p_quic_close"]
opaque close (ep : @& Endpoint) (conn : UInt64) (transport : Bool) (code : UInt64)
  (reason : @& String) (now : UInt64) : IO Unit

/-- The close of a listener: refuse every server connection that has
not finished its handshake, with the transport error `code` and a
reason. The endpoint takes no new connection after it. -/
@[extern "leanp2p_quic_refuse_pending"]
opaque refusePending (ep : @& Endpoint) (code : UInt64) (reason : @& String) (now : UInt64) :
  IO Unit

/-- Open a stream: its id, `openBlocked` when the peer allows no more
streams now, or `openGone` when the connection is gone. -/
@[extern "leanp2p_quic_open_stream"]
opaque openStream (ep : @& Endpoint) (conn : UInt64) : IO UInt64

/-- Append bytes to a stream, and the FIN after them when `fin` holds:
the count of the bytes the peer has not acknowledged, or
`writeRefused`. -/
@[extern "leanp2p_quic_stream_write"]
opaque streamWrite (ep : @& Endpoint) (conn : UInt64) (stream : UInt64)
  (bytes : @& ByteArray) (fin : Bool) : IO UInt64

/-- Return the credit of `n` read or dropped bytes of a stream to the
peer. -/
@[extern "leanp2p_quic_stream_consume"]
opaque streamConsume (ep : @& Endpoint) (conn : UInt64) (stream : UInt64) (n : UInt64) : IO Unit

/-- Let the peer open one more stream: one of its streams is over, and
the application has accepted it. -/
@[extern "leanp2p_quic_grant_stream"]
opaque grantStream (ep : @& Endpoint) (conn : UInt64) : IO Unit

/-- Reset both directions of a stream with the application error
`code`: RESET_STREAM and STOP_SENDING. -/
@[extern "leanp2p_quic_stream_reset"]
opaque streamReset (ep : @& Endpoint) (conn : UInt64) (stream : UInt64) (code : UInt64) : IO Unit

/-- The next event, if one waits. -/
@[extern "leanp2p_quic_next_event"]
opaque nextEvent (ep : @& Endpoint) : IO (Option EventRaw)

/-- The next datagram to send, and its destination, if one waits. -/
@[extern "leanp2p_quic_next_packet"]
opaque nextPacket (ep : @& Endpoint) : IO (Option (ByteArray × ByteArray))

/-- The ALPN protocol of a connection; empty when none. -/
@[extern "leanp2p_quic_alpn"]
opaque alpn (ep : @& Endpoint) (conn : UInt64) : IO String

/-- The peer's address of a connection; empty when the handle names no
connection. -/
@[extern "leanp2p_quic_remote"]
opaque remote (ep : @& Endpoint) (conn : UInt64) : IO ByteArray

end QuicNative
