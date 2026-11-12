# leanp2p quic: architecture

`net/quic` is the QUIC transport (RFC 9000) over UDP. It binds ngtcp2,
a mature C implementation, through a small shim behind a Lean
interface: the FFI-first path of root ARCHITECTURE §4 ("FFI first, Lean
later"; PRINCIPLES 4.1). The TLS 1.3 handshake inside QUIC (RFC 9001)
runs on a `Tls.Context` of `net/tls`, so the TLS settings have one
home. The caller's certificate check runs inside the handshake, as
over TCP. The package knows no protocol above QUIC (§2; PRINCIPLES 4.3): the
caller names the ALPN protocol through the context, and gives the
check. `libp2p/quic` is its caller (root PLAN W4.4).

## Modules

| Module | Holds, and why |
|---|---|
| `upstream/` | the pinned ngtcp2 tree: `UPSTREAM.toml` (the repository, the release, the commit, the file list), `SHA256SUMS`, `COPYING` (MIT), and `pristine/`, the files of the tag the library and its OpenSSL glue need ("The native build") |
| `scripts/verify-upstream.py` | the check of the pin: offline over the hashes and the tree, and against a clone of the pinned commit |
| `native/include/` | the two build-support headers CMake would write: `config.h` and `ngtcp2/version.h` |
| `native/c/quic_shim.c` | the shim: the endpoint object, its connections, the send buffers of the streams, and the two queues for the Lean side |
| `native/QuicNative.lean` | the `@[extern]` declarations of the shim, one per exported function, the event kinds with their conformance theorem, and `udpBind`, the bind with no address reuse ("Decisions", the exclusive bind) |
| `native/lakefile.lean` | the nested Lake package that compiles ngtcp2 and the shim into one archive (PRINCIPLES 4.2) |
| `Quic/Constants.lean` | every number of the package: the transport parameters, the windows, the timeouts, the queue sizes, and the error codes; one home each (§3.8) |
| `Quic/Error.lean` | `Quic.Error`, the one error inductive of the package (§3.5), one arm per way a connection ends |
| `Quic/Address.lean` | the `quic-v1` multiaddr, its socket address, and the shim's address bytes, a codec over the byte model with its round trip as a theorem |
| `Quic/View.lean` | the types the application sees (`Quic.Conn`, `Quic.Admitted`, `Quic.Command`) and the views over the loop's command queue: `Quic.Conn` and `Streams.Stream` |
| `Quic/Loop.lean` | the loop's state and steps, the reader, and the ticker: the one task that calls the shim, and the two that feed it |
| `Quic/Endpoint.lean` | `Quic.dial`, `Quic.listen`, `Quic.Listener`, and `Quic.Bounds`: an endpoint on a bound socket, and its three tasks |
| `Quic.lean` | the package root, one import line per submodule |

## Public surface

- `Quic.dial ctx addr check clock abort : Async (Except Error Conn)`: a
  connection to a `quic-v1` address, once its handshake has finished.
  `check : ByteArray → Option String` decides the peer's certificate
  inside the handshake. The close of the optional `abort` channel ends
  a dial still in its handshake with `.ended`, as a host's shutdown
  closes its pending connections (root §5.5). The dial has its own UDP
  socket, and the connection's `join` ends it.
- `Quic.listen ctx addr admit clock bounds : Async (Listener α)`: a
  listener on a `quic-v1` address. `admit` decides each new connection
  by its two addresses when its first datagram arrives, before any state
  exists for it ("The admission"). `none` refuses the connection with
  CONNECTION_REFUSED. `some` gives its check and a value of the
  caller's, and the value comes back with the connection. `bounds`
  holds the bounds of new connections, the constants by default ("Flow
  control and the bounds"). `Quic.admitAll check` admits every
  connection. `accept` answers each connection with its value once its
  handshake has finished. `close` stops the accepts and ends the
  connections still in their handshake; the connections it gave stay
  open. After `close`, `accept` still gives the connections in its
  queue and then `none`, as quic-go's `Accept` drains its queue. The
  caller closes each one. `join` ends once the listener is closed and
  its last connection has ended.
- `Quic.Conn`: the peer's certificate (DER) that the check accepted,
  the selected ALPN, both addresses, `openStream`, `accept`, `close`
  (an application error code and a reason), and `join`.
- The streams are `Streams.Stream` values: `read`, `write`, `close`
  (our FIN), and `reset`.
- `Quic.handles`, `Quic.socketAddress?`, `Quic.multiaddrOf`: the
  address shape of the package. `Quic.ShimAddr` is the shim's address
  layout, with `ShimAddr.decode_encode`.

## The endpoint

ngtcp2 is a state machine with no I/O: the caller feeds it datagrams
and the time, and takes its packets. Its header lists what it leaves to
the caller: the socket, the routing of a datagram to its connection by
connection ID, the send buffer of each stream until the peer
acknowledges it (`acked_stream_data_offset`), the return of
flow-control credit (`ngtcp2_conn_extend_max_stream_offset`,
`ngtcp2_conn_extend_max_offset`), and the server's new connections and
version negotiation.

The shim does these in C, inside one endpoint object per UDP socket.
Each call takes the time from the caller, in milliseconds of the
caller's clock, and leaves its results in two queues: the events and
the datagrams to send. The shim opens no socket, starts no thread, and
reads no clock.

The path of a packet is ngtcp2's. The shim hands each datagram to its
connection with the datagram's own source, and never moves the
connection itself: ngtcp2 moves only after a packet from a new address
decrypts, and validates the new path (RFC 9000 §9). Each packet goes to
the path ngtcp2 writes for it (`ngtcp2_conn_writev_stream`, `path`). So
a datagram from a spoofed source cannot decrypt, and it moves nothing.
The peer's address that `Quic.Conn` reports is ngtcp2's current one.

The Lean side is the shell of root §3.3, with the state machine in C:

- **The loop** is the one task that calls the endpoint. Each turn it
  writes the endpoint's packets to the socket, then parks on four
  sources at once (`Conc.select`): a datagram of the reader, a command
  of a view, a tick at the endpoint's earliest timer, and a listener's
  close. It hands the input to the shim and drains the events into the
  views. Once the listener's close has come, the loop leaves that park
  out. A closed channel answers every receive at once, so the loop
  would spin until its last connection ended.
- **The ticker** runs a `Conc.Alarm` on the `Clock` seam (root §3.3).
  The loop gives it the shim's earliest timer each time that time
  changes, and it arms one timer per due time. So a turn that leaves
  the due time as it was arms none, and a datagram that opens no
  connection costs no timer.
- **The reader** reads the socket and posts each datagram to the loop
  through a bounded queue.
- **The views** are `Quic.Conn` and `Streams.Stream`. They talk to the
  loop only through queues, so the endpoint sees one caller.

The loop's own tables, the connections and their streams, are plain
data threaded through its recursion. No other task reads them, so they
need no cell (PRINCIPLES 3.3).

## The certificate check

The handshake's `SSL` comes from the `Tls.Context`, whose verify
callback runs the caller's check and enforces the one-certificate
chain (`net/tls`, "The certificate check"; "One context for both
transports"). The shim attaches each connection's check to its `SSL`
(`leanp2p_tls_attach_check`). A refusal fails the handshake inside
libssl, and libssl sends the alert `bad_certificate`. ngtcp2 carries
the alert as the transport error 0x100 plus the alert: CRYPTO_ERROR
0x12a (RFC 9001 §4.8; `ngtcp2_conn_get_tls_alert2`). When a client
sends no certificate, the server sends `certificate_required`, 0x174.

A dial gives one check. A listener gives an admission: when a datagram
would open a new connection within the shim's bounds, `QuicNative.recv`
answers so, and the loop asks the admission. A refusal goes to
`QuicNative.refuse`, which sends CONNECTION_REFUSED and keeps no state;
an admission's check goes to `QuicNative.accept`. So a caller that
reads a clock for its check reads it once per handshake, at its start,
as the TLS value over TCP does.

## The admission

The listener's caller decides each new connection before it costs a
handshake, as the host decides a TCP connection at its accept, before
its upgrade. go-libp2p asks its resource manager at the same point of
a QUIC handshake (`vendor/go-libp2p/config/config.go`, `ConnContext`).
An admission carries a value of the caller's, a resource scope for the
libp2p value, and its release. The loop keeps the admission with the
connection until the accept queue takes the connection; after that the
receiver owns the value. A connection that ends before then (its
handshake failed, the queue was full, the endpoint ended) runs the
release once.

## The ALPN

RFC 9001 §8.1: "endpoints MUST use ALPN", and a connection that
negotiates no application protocol closes with `no_application_protocol`
(0x178). libssl refuses a client whose offer the server does not
support, with that alert (`tls_handle_alpn`). It enforces the QUIC rule
for a missing offer only inside its own QUIC stack, which ngtcp2's glue
does not run: the glue calls `SSL_do_handshake` directly. So the shim
checks at the handshake's end, and closes a connection with no ALPN
with the alert itself. Go (`checkALPN`, `negotiateALPN`) and rustls
make the same check for QUIC.

## The parameters

The endpoint takes every number from `Quic/Constants.lean`
(`QuicNative.endpointNew`). The go reference's QUIC configuration sets
some (`vendor/go-libp2p/p2p/transport/quicreuse/config.go`, `config.go`
in the table), and it keeps quic-go v0.62.0's default for the rest
(`vendor/go-libp2p/go.mod`, line 56; the defaults are in quic-go's
`internal/protocol/params.go`, `params.go` in the table):

| Parameter | Value | Source |
|---|---|---|
| bidirectional streams the peer may open | 256 | `MaxIncomingStreams`, `config.go` |
| unidirectional streams | 0 | libp2p opens none; go allows 5 for WebTransport |
| stream receive window | 512 KiB at the start, up to 10 MiB | quic-go's `DefaultInitialMaxStreamData` (`params.go`, line 19); `MaxStreamReceiveWindow`, `config.go` |
| connection receive window | 768 KiB at the start, up to 15 MiB | quic-go's `DefaultInitialMaxData`, 1.5 times the stream window (`params.go`, lines 16 and 22); `MaxConnectionReceiveWindow`, `config.go` |
| keep-alive | 15 s | `KeepAlivePeriod`, `config.go` |
| idle timeout | 30 s | quic-go's `DefaultIdleTimeout` (`params.go`, line 94) |
| handshake deadline | 30 s | the unauthenticated deadline of root §5.4, `Streams.unauthDeadlineMs` |
| QUIC version | 1 (RFC 9000) | `Versions: []quic.Version{quic.Version1}`, `config.go` |
| largest datagram read | 65527 bytes | the default `max_udp_payload_size` of RFC 9000 §18.2 |
| accept queue of a listener | 32 | quic-go's `MaxAcceptQueueSize` (`params.go`, line 54) |
| datagrams queued for the loop | 1024 | quic-go's `MaxServerUnprocessedPackets` (`params.go`, line 40) |
| unacknowledged bytes per stream before a write parks | 1 MiB | ours ("Flow control and the bounds") |
| server connections in their handshake | 32 | go-libp2p's transient `ConnsInbound` on a minimal node (`vendor/go-libp2p/p2p/host/resource-manager/limit_defaults.go`, lines 23 and 686 to 687); quic-go keeps no such count |
| connections in their handshake past which a client proves its address | 16 | half the cap, go-libp2p's split (`conn_limiter.go`) |
| closing periods a listener keeps | 64 | ours, twice the cap; no spec or reference gives a count ("Flow control and the bounds") |
| the Retry token's lifetime | 30 s | the handshake deadline, quic-go's `maxRetryTokenAge` |
| the orderly close | application error 0 | go-libp2p's `Close` (`vendor/go-libp2p/p2p/transport/quic/conn.go`, lines 42 and 43) |
| the code of a stream reset | application error 0 | go-libp2p's `reset` constant (`vendor/go-libp2p/p2p/transport/quic/stream.go`), sent by its `Reset` in both directions |

The windows start small and grow, as quic-go's do: ngtcp2's
auto-tuning (`ngtcp2_settings.max_stream_window`, `max_window`) raises
a window while the reader keeps up, to its ceiling.

## Flow control and the bounds

- **Receive.** A peer cannot send past the window we granted: ngtcp2
  ends the connection with `FLOW_CONTROL_ERROR` when it tries. A
  stream's inbox therefore holds at most the stream's window, and the
  connection's inboxes together at most the connection's window. A read
  returns the credit for its bytes. So the inbox needs no cap of its
  own (root §5.1; PRINCIPLES 3.4).
- **Send.** QUIC may send a byte again until the peer acknowledges it
  (RFC 9000 §13.3). So the shim keeps every unacknowledged byte, in
  chunks that never move, since ngtcp2 holds pointers into them. A
  write returns at once while the stream's unacknowledged bytes stay
  under `streamSendCap`. Past the cap, it returns after the peer's
  acknowledgments. That bounds the memory one stream holds on our
  side. A flush offers each stream with bytes in turn. A stream that
  the flow window holds leaves that flush alone, so a peer that holds
  back credit on some streams stalls none of the others. ngtcp2's
  pacer spreads the packets. The shim reports each burst
  (`ngtcp2_conn_update_pkt_tx_time`), and the pacer's time is one of
  the timers the loop wakes at.
- **Streams.** A stream the peer opened gives its stream credit back
  once it is over and the application has accepted it, as quic-go's
  does (`streams_map_incoming.go`, `deleteStream`). So the peer has at
  most `maxStreamsBidi` streams open or unaccepted. The accept queue of
  a connection holds as many, so it never fills.
- **Datagrams.** The reader's queue holds `datagramQueueCap`
  datagrams. A full queue parks the reader, and the socket's buffer
  fills. The kernel then drops the excess, and QUIC's loss recovery
  sends it again.
- **Handshakes.** Each server connection costs an ngtcp2 connection and
  a TLS session before its peer has proved anything. So the shim bounds
  these connections before any state exists (`admit_initial`). At
  `maxHandshakes` connections in their handshake, a new client gets
  CONNECTION_REFUSED in a stateless Initial
  (`ngtcp2_crypto_write_connection_close`). From `retryThreshold`, half
  the cap, a client that has not proved its address gets a Retry (RFC
  9000 §8.1.2) and no state. A spoofed source never sees the Retry. So
  spoofed Initials fill half the cap at most, and the clients that
  answer keep the other half. go-libp2p splits its unverified
  connections the same way
  (`vendor/go-libp2p/p2p/host/resource-manager/conn_limiter.go`,
  `newVerifySourceAddressRateLimiter`). The Retry token binds the
  client's address and its first DCID under a random secret of the
  endpoint. It lives as long as the handshake deadline, as quic-go's
  does (`config.go`, `maxRetryTokenAge`). A token that fails the check
  gets INVALID_TOKEN. Each connection in its handshake ends at the 30 s
  deadline, and a listener's close ends them all. The caller's
  admission ("The admission") runs after these bounds, and the host's
  resource manager counts the rest.
- **Routing.** A table by connection ID routes each datagram in one
  lookup. It holds every live ID of a connection, the DCID of its
  client's first packets, and the IDs of each closing period. ngtcp2
  reports the IDs it issues (`get_new_connection_id2`) and the IDs it
  retires (`remove_connection_id`). The table hashes an ID under a
  random seed, so a peer cannot aim its lookups at one bucket. The only
  IDs a peer chooses are the first DCIDs of its handshakes, and the cap
  bounds those.
- **Closing periods.** A listening endpoint keeps at most
  `maxClosingPeriods` records, and past that count the oldest goes.
  Each record lives three PTOs ("The end of a connection").
- **Memory.** The shim allocates the end event of a connection with the
  connection. So the end always reaches the loop, and the loop wakes
  every view. Another event, a stream's record, or a write's chunk can
  find no memory. That ends its connection with INTERNAL_ERROR, as an
  ngtcp2 callback failure does. A datagram that finds no memory is
  lost, as the network may lose it, and QUIC's loss recovery sends its
  frames again.
- **Timers.** The loop arms a timer only when the shim's earliest timer
  changes ("The endpoint", the ticker). A datagram that opens no
  connection changes no timer, so a flood of them arms none.

## The streams

The two directions of a stream end apart (RFC 9000 §3):

- the peer's RESET_STREAM ends its sending part, so our reads end with
  `.reset`, after the bytes that came before it;
- the peer's STOP_SENDING ends our sending part, so our writes end
  with `.reset`, and our reads go on. ngtcp2 answers with the
  RESET_STREAM that RFC 9000 §3.5 asks for (`conn_recv_stop_sending`);
- our `reset` sends both, as the go reference's `Reset` does. The loop
  drops the bytes that wait in the inbox and returns their credit to
  the peer at once. ngtcp2 returns the credit only for the bytes it
  never handed to us (`conn_recv_reset_stream`).

A write answers once the shim holds the bytes for sending, under
`streamSendCap`. From there QUIC owns them and sends them again until
the peer acknowledges them, as a TCP stack owns the bytes of a finished
socket write: that is "on the wire" in the `Stream` contract.

## The end of a connection

A connection ends in one of seven ways, each its own event of the shim
and its own arm of `Quic.Error`:

| End | Event | Answer of `join` |
|---|---|---|
| an application close with code 0, ours or the peer's, or the peer's transport close with NO_ERROR | `connClosed` | `.ok` |
| an application close with another code | `connClosed` | `.closed code` |
| our TLS refused the peer's certificate | `connRefused` | `.refused` |
| we closed on a transport error: a protocol error, a TLS failure, no ALPN, a full accept queue, a listener's close | `connFailed` | `.failed code` |
| the peer closed on a transport error, a refusal of our certificate included | `peerFailed` | `.peerFailed code` |
| the handshake deadline | `connTimeout` | `.timeout` |
| the idle timer (RFC 9000 §10.1) | `connIdle` | `.idle` |
| a stateless reset of the peer (RFC 9000 §10.3), or a drop that ngtcp2 asked for | `connDropped` | `.dropped` |

A stateless reset moves ngtcp2 to draining, as the peer's close does,
so the shim tells them apart by the `recv_stateless_reset2` callback.

The handshake deadline wins over the idle timer, as in quic-go's run
loop (`ErrHandshakeTimeout` before `ErrIdleTimeout`). ngtcp2 tests the
idle timer first, and that timer starts with the connection, so a peer
that never answers would end on both at the same instant. The shim
tests the deadline before it hands the timers to ngtcp2.

A listening endpoint keeps the closing period of each connection it
closes (RFC 9000 §10.2), as quic-go does. For three PTOs it holds the
connection's IDs, the client's first DCID, and the CONNECTION_CLOSE it
sent. It answers a packet for one of those IDs with the close again,
on the 1st, 2nd, 4th, 8th, ... packet (`closed_conn.go`,
`closedLocalConn`). So a lost close still reaches the peer. A client
whose refusal was lost gets the refusal again, in place of a second
handshake. The record holds no ngtcp2 state.

At the end the loop wakes every view that parks on the connection. The
inboxes and the accept queue close, and every write, open, and dial
that waits gets its answer (PRINCIPLES 3.1). A dialing endpoint ends
with its connection, as quic-go's single-use dial transport does
(`transport.go`, lines 334 to 336). A listening endpoint ends once its
listener is closed and its last connection has ended. At its end the
loop closes the reader's queue. It also wakes the reader's parked
receive with a datagram to the socket itself, and the reader's park
ends ("Decisions", the UDP socket).

## Owned contracts

1. **One caller per endpoint.** Only the loop calls the shim, so the
   endpoint needs no lock.
2. **Every park has a close** (PRINCIPLES 3.1). The reader parks on
   the promise of its receive. The loop's end wakes that promise with a
   datagram, or resolves it when the send fails. The reader also parks
   on its queue, which the loop's end closes. The loop parks on its
   queues and the ticks, and on `stopAccepting` until that channel
   closes. The ticker parks on its alarm and the tick queue, which the
   loop's end closes. A dial parks on its answer slot and its abort.
   The close of the abort ends the connection, and that end answers the
   slot. A view parks on an inbox, an accept queue, or an answer slot.
   The end of its connection closes or answers each of them.
3. **Every task has an owner** (PRINCIPLES 3.2). The loop, the reader,
   and the ticker belong to the endpoint's task set. A dialed
   connection's `join` joins the tasks of its dialing endpoint, and a
   listener's `join` joins the tasks of its listening endpoint.
4. **Bounded inputs** (root §5.1; "Flow control and the bounds"). The
   windows bound the receive side, and `streamSendCap` the send side.
   `datagramQueueCap` bounds the datagrams, `maxHandshakes` the
   connections in their handshake, and the deadline each handshake. The
   stream credit bounds each accept queue. `maxClosingPeriods` and three
   PTOs bound the closing periods. Past `retryThreshold`, an Initial
   from an unproved address keeps no state. A datagram that opens no
   connection arms no timer.
5. **The time is the caller's.** Every shim call takes the time from
   the `Clock` seam. So the shim never reads a clock, and a test clock
   drives every timer.
6. **No connection before the check.** The check runs inside the
   handshake, and a `Conn` exists only for a certificate it accepted.
7. **An ended endpoint releases its socket.** The loop's end leaves no
   receive armed. So the socket closes with its last reference, and its
   port binds again.
8. **The shim borrows every argument** (PRINCIPLES 4.1). An endpoint
   holds a reference to its TLS context. Each connection's `SSL` holds a
   reference to its check, and `SSL_free` drops it.
9. **No admission leaks.** The loop releases a connection's admission
   once, unless the accept queue took the connection. After that, the
   receiver owns the admission.
10. **Each endpoint holds its port alone.** The shim binds the socket
    with no address reuse ("Decisions", the exclusive bind). So no other
    socket shares the port, and a listen on a port in use fails.

## The native build

`upstream/pristine/` holds the files of the ngtcp2 tag `v1.24.0`
(commit `956e7b4cfb6762312434ecdddb796baf0775f12a`,
`https://github.com/ngtcp2/ngtcp2`) that the library and its OpenSSL
glue need: every `lib/ngtcp2_*.c` and `lib/ngtcp2_*.h`,
`lib/includes/ngtcp2/ngtcp2.h`, `crypto/shared.{c,h}`,
`crypto/ossl/ossl.c`, and the two crypto headers the shim includes.
`UPSTREAM.toml` lists them, and `SHA256SUMS` holds the hash of each,
in the same order. `scripts/verify-upstream.py` checks the hashes, and
that no other file is present, with no network. With `--clone DIR` it
also compares every file with the pinned commit of an ngtcp2 clone,
byte for byte. No patch applies, so the pinned tree is the compiled
tree, as in `codec/snappy` minus the patch step.

`native/include/` holds what CMake would generate. `version.h` fills in
the two values of `version.h.in`. `config.h` answers the build probes
with `__has_include`, so the build needs no configure step. The pinned
sources test no other configuration macro. `__has_include` cannot see
a function, so `config.h` leaves `HAVE_EXPLICIT_BZERO` and
`HAVE_MEMSET_S` unset. `ngtcp2_secure_clear` then clears through a
volatile `memset` pointer, which is upstream's own fallback.

`native/lakefile.lean` compiles the units of upstream's
`ngtcp2_SOURCES` list with the defines the upstream CMake build sets
for a static library (`HAVE_CONFIG_H`, `BUILDING_NGTCP2`,
`NGTCP2_STATICLIB`). The pinned units build with no `-Werror`: a new
compiler's warning in upstream code must not stop the build. The shim
builds with `-Wall -Werror`.

## Decisions

- **ngtcp2, against OpenSSL 3.5's own QUIC.** Both run TLS 1.3 on the
  OpenSSL the stack already binds. ngtcp2 takes the time and the
  datagrams from its caller, so the loop of root §3.3 and the `Clock`
  seam drive it. The suites own the socket. OpenSSL's QUIC keeps
  its event loop and timers inside the library. The reference stacks
  bind QUIC libraries of their own languages: quic-go (go-libp2p),
  quinn (rust-libp2p), lsquic (nim-libp2p). etheorem/leanp2p#92 records
  the comparison and the check that ran the libp2p TLS shape over
  ngtcp2.
- **Compiled from the pinned source, against the toolchain's
  OpenSSL.** The Lean toolchain links its own static OpenSSL 3.6.0 into
  every executable. A system `libngtcp2_crypto_ossl.so` would load the
  system's `libssl` beside it, two OpenSSLs in one process, with our
  `SSL` objects passing between them. Compiled into our archive, ngtcp2
  resolves every OpenSSL call to the toolchain's copy, which has the
  `SSL_set_quic_tls_cbs` hook ngtcp2's glue needs. `codec/snappy`
  builds its library from pinned sources the same way.
- **v1.24.0.** One of the two versions the mutual-authentication check
  of etheorem/leanp2p#92 ran against, and the newer one. The shim uses
  its current callbacks (`get_new_connection_id2`,
  `get_path_challenge_data2`, `recv_stateless_reset2`, deprecated
  forms since 1.22.0, and `recv_stop_sending`, new in 1.24.0) and the
  `…2` accessors that replace the calls 1.23.0 deprecated.
- **The check inside the handshake, each listener check at its own
  time.** A refusal reaches the peer as its TLS alert, as over TCP, and
  no connection exists for a refused certificate. A listener lives
  longer than one handshake, so a check made once would carry a stale
  time. The listener's caller makes a check for each handshake.
- **One socket per dial.** A dial binds its own UDP socket on a port
  the system picks, and the connection's end closes it. The go
  reference shares one socket per address family across dials and
  listeners (`quicreuse`), so its dials leave from its listening port.
  Neither side depends on the other's choice.
- **The state machine is ngtcp2's, in C.** Root §3.3 asks for pure
  cores; the FFI-first rule of §4 puts a mature implementation behind
  the interface first. The loop shell has the shape a pure core would
  take, and a native core can replace the shim behind the same
  `Quic.Conn` and `Streams.Stream` views.
- **A Retry under load, no stateless reset, no migration of ours.** The
  server sends a Retry only past `retryThreshold` ("Flow control and
  the bounds"): below it, a Retry would cost every client a round trip
  for no gain. The endpoint sends no stateless reset, so its reset
  tokens need no secret to derive them again. ngtcp2 still validates a
  peer that moves to a new path. The dialer takes a Retry (RFC 9000
  §17.2.5.2) through `ngtcp2_crypto_recv_retry_cb`, and takes a peer's
  stateless reset as the end of the connection.
- **Post-handshake refusals by the host send code 0.** `MuxSession.close`
  takes no code, on either transport, so a session the host's gater
  refuses after the handshake closes with the orderly code. go-libp2p
  sends its `ConnGated`, 0x1007 (`vendor/go-libp2p/core/network/conn.go`),
  which no vendored spec defines. The QUIC value's own refusal, for a
  handshake whose result contradicts its checks, sends
  `Libp2p.Quic.protocolViolation`. A code on `MuxSession.close` is a
  change of a frozen seam (RULES.md, "Working ahead of the tree").
- **The UDP socket is `Std.Async.UDP`, the second exception of root
  §4.1.** `base/conc` wraps `Std.Async` so that no other package
  imports it, apart from `Std.Async.TCP` in `net/streams`. The UDP
  socket is this package's one transport, as TCP is `net/streams`'s.
  The binding stays in `Quic/Loop.lean` (the receive and the send),
  `Quic/Endpoint.lean` (the socket's creation), and
  `native/QuicNative.lean`, whose `udpBind` names the socket type for
  the shim's bind (the next bullet).
  The v4.34 socket has no close: its finalizer closes it when its last
  reference goes. The reader parks on the promise of the native
  receive, as the TCP transport's read does (`Streams/Tcp.lean`).
  `Std`'s receive selector would also wake on a `select`, but it waits
  on the receive with `.block`, which holds a pool thread for each
  datagram.
- **The exclusive bind: the shim binds the socket, with no address
  reuse.** Lean binds every UDP socket with `UV_UDP_REUSEADDR`
  (`vendor/lean4/src/runtime/uv/udp.cpp`, line 106), in v4.34.0, in
  v4.35.0, and in v4.36.0-rc2. `Std.Async.UDP` offers no bind without
  it. On Linux, SO_REUSEADDR lets a port-0 bind take a port that
  another live socket already holds, and the kernel then gives each
  datagram to one of the two sockets. So two dials could share a port,
  and one connection would receive the other's packets. The loop's wake
  datagram (the workaround below) could also reach the wrong socket and
  leave a reader parked forever. The suite met exactly that: a backlog
  check whose dials 1 and 8 held one port hung in a `join`. A listen on
  a port in use would also succeed and split the traffic.

  So `QuicNative.udpBind` binds each endpoint's socket instead of
  `Std`. The shim opens a socket, binds it with no reuse option, and
  hands the descriptor to the `uv_udp_t` inside Lean's socket object
  with `uv_udp_open`. `uv_udp_open` sets the reuse option on the
  descriptor it takes (libuv v1.48.0, `src/unix/udp.c`, line 1040,
  `uv__set_reuse`), so the shim clears SO_REUSEADDR, and SO_REUSEPORT
  where it exists, right after the call. The receive and the send stay
  on `Std.Async.UDP`. A port another socket holds now fails with
  EADDRINUSE, as quic-go's `net.ListenUDP` does, and no later bind can
  share the port. Three checks pin it: a second listen on a live
  listener's address fails, and a socket that `Std` binds, with its
  reuse option, takes neither a live listener's port nor a live dial's.
  Each fails under the old bind.

  Two limits stay. The shim calls `uv_udp_open` without Lean's loop
  lock, which C cannot reach. That is safe because the socket is fresh
  from `Socket.mk`: libuv's loop thread touches no handle that has no
  receive or send started. And between `uv_udp_open` and the clear of
  the option, for well under a microsecond, the socket has the reuse
  option set. Only a socket that binds with reuse could share the port
  in that window. In this stack every UDP bind goes through
  `udpBind`, so only another process's socket could, and only if the
  kernel's pick for it landed on this port in that window.

  **At a toolchain upgrade**, the guard in `native/c/quic_shim.c`
  (`LEAN_VERSION_MINOR == 34`) fails the build. Lift it only after these
  checks, against the new toolchain's sources:
  1. `lean_uv_udp_socket_object` in `src/runtime/uv/udp.h` still has
     the `uv_udp_t` pointer as its first field.
  2. `lean_uv_udp_new` in `src/runtime/uv/udp.cpp` still creates the
     handle with `uv_udp_init`, with no descriptor, so `uv_udp_open`
     can take one.
  3. The libuv in the toolchain (`strings lib/libuv.a`) still exports
     `uv_udp_open`. Read its `uv_udp_open` again. If it no longer sets
     a reuse option, the clear after it does no harm.
  4. If `lean_uv_udp_bind` no longer passes `UV_UDP_REUSEADDR`, or
     `Std.Async.UDP` gains a bind without reuse, use that bind. Then
     delete `leanp2p_quic_udp_bind`, `QuicNative.udpBind`, and the
     guard, and keep the three checks.

  Then update the `vendor/lean4` pin in `VECTORS.lock` to the new tag,
  run `scripts/vendor-pull.sh`, and run the QUIC suite and
  `scripts/quic-interop.sh`.
- **Workaround: the UDP cancel of Lean v4.34 leaks the socket. Remove
  it at toolchain v4.36.0 or later.** In v4.34.0 and v4.35.0,
  `lean_uv_udp_cancel_recv` stops a pending receive but never drops the
  socket reference that the receive took for the event loop. So a
  socket whose receive was cancelled never closes, and its port stays
  bound for the life of the process. Lean fixed it in v4.36.0-rc2: the
  cancel now drops that reference. The TCP cancel was always right,
  so `net/streams` is not affected.

  The workaround: the loop's end never cancels a pending receive. It
  sends an empty datagram to the socket itself. The receive's callback
  then runs and drops the reference, and the socket closes once the
  views let go of it. Only when that send fails does the end take the
  fallback path. It resolves the parked promise itself and cancels the
  receive, and that one socket stays open.

  At the upgrade, delete:
  - the datagram to itself in `stopReading` (`Quic/Loop.lean`), so the
    fallback path, resolve then cancel, becomes the only path;
  - `ReadState.fallback` and the reader's test of it, since every stop
    then resolves the promise itself;
  - `Shared.selfAddr`, and `Quic.selfAddress` (`Quic/Address.lean`)
    with its three checks in `Tests/Quic.lean`.

  Keep the check "an ended listener's port binds again"
  (`Tests/Quic.lean`, `releaseChecks`). It fails under the leak, so it
  shows whether the upgrade fixed it. Each site above carries the
  marker `TODO(lean v4.36)`.

## What the package must not depend on

- Nothing of the libp2p group, and no mention of it in a `.lean` file
  (§2; the import lint, rule 2).
- From the net group, `net/streams` (`Stream`, the address helpers of
  `Streams.Tcp`, `unauthDeadlineMs`) and `net/tls` (`Tls.Context`).
- From the codec group, `codec/multiformats`: the multiaddr.
- From `base`, `base/conc`: `Async`, `Chan`, `OnceRef`, `TaskSet`,
  `Clock`, and `select`.
- No crypto import: ngtcp2's glue brings OpenSSL's primitives.
