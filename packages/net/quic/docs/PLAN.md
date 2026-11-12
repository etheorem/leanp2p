# leanp2p quic: plan

This plan refines the root `docs/PLAN.md` for `net/quic`. The root plan
owns the order across packages (PLAN.md, "How to read this plan").
Unit 1 below is the engine half of root unit W4.4; `libp2p/quic`
carries the libp2p half. The done-when of the unit is the root row
plus the root definition of done: the surface follows ARCHITECTURE
§4, the owned contracts hold, the carried tests pass, the suite passes
with `LEAN_NUM_THREADS=1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W1.1, W4.1, W5.11 | the pinned ngtcp2 and its check, the shim, the bindings, the endpoint loop, `Quic.dial`, `Quic.listen`, and the stream views | the milestones below pass |

Units 0 and 1 are done. The suite is `Tests/Quic.lean`.

## Consumers

- `libp2p/quic` (W4.4): the `SecuredTransport` value over `Quic.dial`
  and `Quic.listen`, with the libp2p certificate check.
- `cli/` (W5.9): the harness's `quic-v1` cells, through `libp2p/quic`.

## Test milestones (unit 1)

The suite runs endpoints over loopback UDP: QUIC's transport is the
socket, as the TCP suite's is (root §6). The engine checks give the
endpoint a check that takes any certificate, so the certificates carry
an arbitrary extension.

- The address codec: socket addresses of both families, at both ends
  of the port range, go to the shim's bytes and back, and the bytes
  follow the proved layout (`ShimAddr.decode_encode`). `Quic.handles`
  takes a `quic-v1` multiaddr and refuses the draft `/quic` and a TCP
  address.
- The handshake: both sides select the ALPN, and both hold the peer's
  certificate.
- A stream echo after our FIN: the peer's reply arrives after the FIN
  (PRINCIPLES 2.2).
- 12 MiB on one stream, past `streamSendCap` and past the 10 MiB stream
  window, arrive whole.
- 32 streams at once each echo.
- Our reset with bytes in the inbox: the next read answers `.reset` at
  once, ahead of the loop's drop of those bytes, and a write fails. The
  peer's reset ends our reads with `.reset`, and its STOP_SENDING ends
  our writes with `.reset`.
- The dialer's close: both joins answer an orderly end, and the peer's
  accept answers `none`.
- A closed listener's accept answers `none`. A listener closed while a
  connection lives does not join until that connection ends, then
  joins.
- An ended listener releases its socket: a new listener binds its port.
- Each endpoint holds its port alone: a second listen on a live
  listener's address fails. A socket that `Std` binds, with its reuse
  option, takes neither a live listener's port nor a live dial's. Each
  check fails under `Std`'s own bind.
- The echo over IPv6 loopback (`/ip6/::1/udp/0/quic-v1`): the listener
  and the peer's address are `ip6`. A host that cannot bind `::1`
  records a skip with the reason.
- Of `listenBacklog + 1` dials to a listener that accepts nothing, the
  listener refuses exactly one with CONNECTION_REFUSED, whichever
  handshake ends last. Each other dialer's close ends in order, and the
  closed listener still gives the queued connections, each ended with
  its dialer.
- A dial to a UDP socket that never answers, on the test clock: one
  second before the handshake deadline it still waits, and past the
  deadline it ends with `.timeout`, the deadline's own error.
- The close of a dial's abort channel ends the dial still in its
  handshake with `.ended`, before its deadline.
- 200 datagrams that open no connection, then one connection, arm
  fewer than 100 timers on the listener's clock: the loop arms a timer
  only when the shim's earliest timer changes.
- The peer's stream credit: the dialer opens `maxStreamsBidi` streams
  and resets each while the listener accepts none; the next open waits,
  and one accept lets it through.
- The reason text of an end event: valid text stays whole, a character
  that the cut split drops its bytes, and bytes that are no UTF-8
  become a placeholder, never an empty text and never a panic.
- A client with another ALPN name gets `no_application_protocol`,
  CRYPTO_ERROR 0x178 (RFC 9001 §8.1).
- A chain of two certificates fails the handshake in both directions:
  the dialer refuses the listener's chain, and the listener refuses the
  dialer's with `bad_certificate` (0x12a) and accepts no connection.
- An application close with a code: both joins answer `.closed` with
  the code.
- The admission: a refused client gets CONNECTION_REFUSED; a failed
  handshake releases its admission once; a handed-over connection
  releases nothing.
- The checks below send datagrams of their own. The suite captures a
  client's first Initial from a real dial and sends it again from a
  socket that never answers: a client with a spoofed source.
  - The cap: three such Initials fill a cap of three, and a real dial
    then gets CONNECTION_REFUSED.
  - The Retry: with a threshold of two and a cap of three, twelve
    spoofed Initials get exactly ten Retry packets. A real dial then
    answers its Retry and connects. So no spoofed Initial past the
    threshold kept state.
  - A forged Retry token gets one Initial in answer and no connection.
  - The closing periods: a listener's close refuses two spoofed
    handshakes while a live connection keeps the endpoint up. With room
    for one record, the suite sends both Initials again, and exactly
    one gets the close again.
  - An unknown version gets a version negotiation packet with the IDs
    swapped and QUIC v1 listed.
- Through a relay that drops one direction or both:
  - the idle timeout, on the test clock: a peer that goes silent ends
    the connection with `.idle`, no earlier than `idleTimeoutMs`;
  - the send cap: a write of twice `streamSendCap` parks while no ACK
    arrives, ends once they do, and its bytes arrive whole.
- The keep-alive, on one test clock for both peers: one and a half idle
  timeouts of silence leave the connection up, and a stream echoes
  after it.
- The suite passes with `LEAN_NUM_THREADS=1` (PRINCIPLES 5.3).
  `LEANP2P_SUITE=quic` runs this suite alone, for a memory checker.

Four paths have no test. Each needs a peer or a fault that the suite
cannot make:

- the close for a missing ALPN: no client the suite can build offers
  none (a `Tls.Context` refuses an empty ALPN, and quic-go refuses to
  dial without one);
- a peer's stateless reset: it carries a token that the peer issued
  under encryption, and our endpoint sends none (ARCHITECTURE,
  "Decisions");
- the pacer's spread of a burst: loopback has no bottleneck that loses
  a burst;
- the paths of memory that runs out (ARCHITECTURE, "Flow control and
  the bounds", the memory bullet): the shim has no fault injection.

## Vector stance

QUIC draws fresh connection IDs and TLS randomness, so no transcript
repeats, and the package carries no vector. `upstream/` pins the
compiled source, and `scripts/verify-upstream.py` checks it. The live
checks are `scripts/quic-interop.sh` (`libp2p/quic`, against go-libp2p's
QUIC transport over quic-go) and the `quic-v1` cells of the W5.9 matrix
(`scripts/interop-matrix.sh`).
