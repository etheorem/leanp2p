# leanp2p streams: plan

This plan refines the root `docs/PLAN.md` for `net/streams`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Unit 1 below is the root unit W4.1, and unit 2 is the root
unit W4.2. The done-when of each unit is the root row plus the root
definition of done: the surface follows ARCHITECTURE §4.7 and §7 row
8, the owned contracts hold, the carried tests pass, the suite passes
under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W1.1, W1.2, W2.1, W2.3 | the streams core, root W4.1: `Connection`/`Listener`/`Transport`, `readExactly`, `BufReader`, `Framing`, `Stream` with `prependBytes` over the loop (§3.3), `Streams/Constants.lean`, the sim transport as the test `Transport` value, and a stub TCP value (`Streams/Tcp.lean`: the mapping between a multiaddr and a socket address in both directions; `dial` and `listen` throw) | the root W4.1 row holds, and the unit 1 milestones below pass |
| 2 | W4.1, W1.1 | the TCP transport, root W4.2: `Streams/Tcp.lean` replaces the stub, with the close-wakes discipline, failed-write teardown, and the deadline wiring for §5.4; the C shim of `shim/` ends the stuck requests of a socket | the root W4.2 row holds, and the unit 2 milestones below pass |

Unit 1 needs W2.1 for the `uvarint` prefix of `Framing`, and W2.3 for
the `Multiaddr` of `Connection`, `Listener`, and `Transport`
(ARCHITECTURE, "What the package must not depend on"). Until those
units merge, the package builds against mocks of them (ARCHITECTURE,
"The mocks").

Unit 0 is done.

## Consumers

- `net/yamux` (W4.3) builds its session over `Connection` and serves
  `Stream` values through its loop.
- `libp2p/core` (W5.2) holds the seam structures that reference
  `Connection` and `Stream` (§3.1, §4.9); the types themselves live
  here.
- `libp2p/security` (W5.3) hands its leftover handshake ciphertext to
  the next reader as data, through the hand-over contract of §4.7.
- Every protocol suite above this package runs over the sim transport,
  and only the transport suite of this plan touches real TCP (PRINCIPLES
  1.4).

## Test milestones (unit 1)

- Sim: dial and listen over the in-memory pair, and an echo exchange
  across the two pipes. A dial to an address with no listener returns
  `none`. A read may split or coalesce writes, so no suite may rely on
  write boundaries; the byte-splitting hostile mode delivers every
  write one byte at a time (the spike's `Connection.byteSplitting`).
- Framing: a length prefix exactly at the cap passes, one over it
  reports `malformed` before any payload read, and a truncated prefix
  reports `truncated` through the `DecodeError` boundary of
  `base/bytes`. The framing core is proved over the byte model, and
  the `ByteArray` path is pinned to it by the generic fuzz harness
  (§6).
- `Stream`: a write completion arrives as `Action.done` or
  `Action.refused` through the loop, and `Stream.write` returns only
  after its tag resolves. `prependBytes` puts the handed-on bytes
  ahead of the bytes the loop delivers.
- TCP addresses: an `/ip4` and an `/ip6` TCP multiaddr map to their
  socket addresses and back. Every other shape maps to `none`,
  `handles` refuses it, and a `dial` or a `listen` of it throws.
- The theorems of ARCHITECTURE, "Theorems", build with no `sorry`. Their
  axioms are the three standard axioms of Lean and the two axioms of the
  varint mock, no others.
- The mocks: the varint mock reproduces the spec examples. The
  multiaddr mock parses each of its four forms, and prints the same
  text again.

## Test milestones (unit 2)

- Close-wakes: a parked read wakes when `close` resolves its promise,
  and it returns EOF; a second `close` is a no-op; a parked accept
  wakes when the listener closes.
- Failed-write teardown: a write that fails tears the connection down,
  and the local read then sees EOF. The suite fails the write for
  real: it drops the peer's end with unread bytes, so the kernel
  resets the connection, and a later write fails on the socket.
- Silent peer: a dial that receives nothing fails at the 30 s deadline
  of §5.4, and the teardown joins every task of the connection.
- Deadline wiring: `withinDeadline` closes the connection on expiry,
  and the parked read ends on its own. A connect that hangs fails at
  the dial deadline: the suite fills the accept queue of a loopback
  listener that never accepts, so the kernel drops the next SYN, and
  it dials that listener on the test clock. No packet leaves the
  machine.
- The RST path of §4.7: a teardown with a write in flight to a peer
  that stops reading aborts the write, and a raw socket on the peer's
  end meets the reset. A raw socket reads below `Connection.read`,
  which answers a reset as EOF.
- The peer's reset (ARCHITECTURE, "Decisions"): a read that meets the
  RST of a dropped peer answers EOF, and the connection is torn down.
- A closed listener stops listening: a dial to it answers `none`, and
  its port takes a new listener.
- The TCP suite over loopback: dial and listen, plus an echo
  exchange. The mss, Noise, and muxer suites of the spike run over
  this transport when their packages land (W5.5, W5.3, W5.4, W4.3),
  as root §7 row 8 records. Root W4.2 depends on W4.1 and W1.1
  only, so those suites are not gates of this unit.
- Both units pass under `+RTS -N1`, the starvation criterion of §6.

## Vector stance

The package has no wire vectors. The framing core closes through
theorems, and the transport contracts close through behavior tests:
the spike's TCP suite and the silent-peer scenario are behavior tests.
The captured transcripts (multistream, Noise) land with the protocol
packages through W0.3 (§6). A wire transcript needs a protocol on top,
and the connection layer below it pins its contracts by behavior
alone.
