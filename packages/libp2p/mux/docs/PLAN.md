# leanp2p libp2p mux: plan

This plan refines the root `docs/PLAN.md` for `libp2p/mux`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Unit 1 below is the root unit W5.4. The done-when of the units
is the root row plus the root definition of done: the surface follows
ARCHITECTURE §4.9, the owned contracts hold, the carried tests pass,
the suite passes under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W4.3, W5.2 | the P0 delivery: integration with the landed Core seam, `Mux.yamux` over the Yamux session, the independent `Mux.test` session, and the constants and adapter tests | the root W5.4 row and the unit 1 milestones below are satisfied |
| 2 | W2.1, W5.2, unit 1 | the mplex value (root W5.10): the message codec, `Mux.mplex`, the go-compatible `(id, initiator)` identity, the half-close rules, and the 1 MiB cap | the root W5.10 row holds, and the unit 2 milestones below pass |

Unit 2 depends on W2.1, on the seam from W5.2, and on the constants
from unit 1, including `Mux.mplexMessageCap`. Unit 2 checks a declared
length against that cap.

Units 0, 1, and 2 are complete.

## Consumers

- The upgrade pipeline (W5.5) picks the muxer after security (§4.9)
  and hands the negotiation leftover through the `ByteArray` argument
  (§4.7).
- The host (W5.6) serves the stream handlers through the `MuxSession`
  the chosen value returns, and joins its completion (§3.1).
- `cli/` (W5.8) and the interop matrix (W5.9) assemble the ordered
  muxer lists (§3.1). Every host offers `[Mux.yamux, Mux.mplex]`, in
  that order. The W5.9 gate is `tcp + /noise + yamux` (root PLAN
  W5.9). A live go-libp2p matrix cannot exercise mplex against v0.50
  and later, so `scripts/mplex-interop.sh` runs `Mux.mplex` against
  go-mplex itself.

## Test milestones (unit 1)

**Constants.** The suite checks `Mux.yamuxId.toString = "/yamux/1.0.0"`,
`Mux.mplexId.toString = "/mplex/6.7.0"`,
`Mux.testId.toString = "/leanp2p/test-mux/1.0.0"`, the pairwise
distinctness of the three ids, and `Mux.mplexMessageCap = 1 MiB`. It
checks `Mux.test.id = Mux.testId`.

**Yamux adapter.** The suite checks `Mux.yamux.id = Mux.yamuxId`. An
initiator open passes an unrelated `ProtocolId` and emits a
window-update SYN of length 0 for stream id `1`, the Yamux client
id. A responder open emits that frame for stream id `2`, the Yamux
server id. The header carries the type, the flags, the stream id,
and the length. One full-duplex stream through public `Mux.yamux`
carries a payload in each direction, and both sessions join cleanly.
A nonempty leftover on the public responder open accepts the remote
stream and delivers its payload. One malformed header makes `join`
return `Core.Error.protocol` with detail
`s!"yamux: {repr Yamux.ProtocolError.malformedHeader}"`. A second
`join` returns that same error. After a clean close, `openStream`
returns `Core.Error.closed` with detail
`s!"yamux: {repr Streams.Error.closed}"`. A thrown connection
`IO.Error` leaves the first `join` and the second `join` as that
same thrown error.

**Yamux session.** Framing, flow control, reset, half-close, hostile
frames, and keepalive stay in the `net/yamux` suite.

**Test muxer.** `Mux.test` is independent of Yamux. The suite covers
its lifecycle and hostile input: the private frame codec, the
incremental parser, the pure state transitions, and deterministic
two-ended sim tests. Those tests cover stream ids, simultaneous
opens, ordered and empty writes, half-close, reset, stream lifetime,
accept and inbox backpressure, terminal races, fairness, and the
copied-byte accounting.

**Runtime.** CI runs both the ordinary and `+RTS -N1` suites; both
are required acceptance gates (§6, PRINCIPLES 5.3).

## Test milestones (unit 2)

- The identity rule (§4.9): two sessions over a sim pair each number
  their streams from zero, and the session keys by `(id, initiator)`,
  so the two id-0 streams coexist, one per initiator, and each session
  map holds `(0, initiator)` beside `(0, non-initiator)` with no
  cross-delivery. The flag bit routes every inbound message to the key
  it names.
- The 1 MiB cap: a declared length one over `Mux.mplexMessageCap` is a
  protocol error, rejected before allocation (§5.1, PRINCIPLES 2.3).
- A header varint that cannot complete within 9 bytes is a protocol
  error, not a request for more bytes; a short prefix stays incomplete
  (§5.2, PRINCIPLES 5.4).
- The half-close suite asserts the spec sentence (§5.3,
  PRINCIPLES 2.2): close ends the write direction of the closer only,
  and the response after our FIN still arrives. The spike's first
  e2e test asserted one shared open flag, so a peer close that
  silenced local writes stayed green for weeks. The rewritten suite
  carries three cases: the reads drain to EOF after a peer close, the
  write direction stays open, and a response sent after our FIN
  arrives. Port all three.
- Reset aborts both directions and retires the stream from the session
  map (§4.9).
- The suite passes under `+RTS -N1` (§6, PRINCIPLES 5.3).
- go-mplex interop: `scripts/mplex-interop.sh` runs `Mux.mplex`
  against go-mplex v0.7.0 over loopback TCP, in both directions. Four
  streams each move `mplexMessageCap + 7` bytes, with a half-close
  before every echo. The check stays outside `lake test`, which takes
  no Go tooling.

## Vector stance

`VECTORS.lock` holds no muxer entry, and `Tests/vectors/` on the spike
branch holds no mplex or yamux file; no muxer wire transcript was
captured. The yamux session carries its own suite in `net/yamux`: the
fixed header bytes, the hostile frames, and the flow-control cases
(the yamux pair, plan). This package pins the unit 1 seam
adaptation through `Mux.yamux` and `Mux.test`. Unit 2 pins the
mplex identity and half-close cases through `Mux.mplex`, and the spike's
four header vectors in `Tests/Mplex.lean`. The live
gate is the go-libp2p interop matrix at W5.9 over `tcp + /noise +
yamux` (root PLAN W5.9); the spike proved that path once, and W5.9
re-runs it against this implementation. The same-node-code-under-both
payoff of PRINCIPLES 1.3 was demonstrated in-process and over loopback.
A live go-libp2p matrix cannot exercise mplex against v0.50 and later;
`scripts/mplex-interop.sh` covers go-mplex directly.
