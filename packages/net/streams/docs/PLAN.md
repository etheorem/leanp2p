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
| 1 | W1.1, W1.2 | the streams core, root W4.1: `Connection`/`Listener`/`Transport`, `readExactly`, `BufReader`, `Framing`, `Stream` with `prependBytes` over the loop (§3.3), `Streams/Constants.lean`, and the sim transport as the second `Transport` value | the root W4.1 row holds, and the unit 1 milestones below pass |
| 2 | W4.1, W1.1 | the TCP transport, root W4.2: `Streams/Tcp.lean` with the close-wakes discipline, failed-write teardown, and the deadline wiring for §5.4 | the root W4.2 row holds, and the unit 2 milestones below pass |

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
  across the splice. A dial to an address with no listener returns
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

## Test milestones (unit 2)

- Close-wakes: a parked read wakes when `close` resolves its promise,
  and it returns EOF; a second `close` is a no-op; a parked accept
  wakes when the listener closes.
- Failed-write teardown: a write that fails tears the connection down,
  the local read then sees EOF, and the peer receives a FIN.
- Silent peer: a dial that receives nothing fails at the 30 s deadline
  of §5.4, and the teardown joins every task of the connection.
- Deadline wiring: `withinDeadline` closes the connection on expiry,
  and the parked read ends on its own.
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
