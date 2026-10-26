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
| 1 | W4.3, W5.2 | the yamux `Muxer` value over the W4.3 session: `Mux.yamux`, the constants module, the `Except.mapError` into `Core.Error`, and the fixed-ids test value | the root W5.4 row holds, and the unit 1 milestones below pass |
| 2 | W2.1, W5.2, unit 1 | the mplex value (P2, §8): the message codec, `Mux.mplex`, the go-compatible `(id, initiator)` identity, the half-close rules, and the 1 MiB cap | the mplex half of the root W5.4 deliverable holds, and the unit 2 milestones below pass |

Unit 2's deps are the package's own call. The root graph lets mplex
follow W5.4 at any time, and the mplex core needs the seam (W5.2) and
no yamux session. Unit 1 comes first because it lays the constants
module and the test-value pattern that unit 2 reuses.

Unit 0 is done.

## Consumers

- The upgrade pipeline (W5.5) picks the muxer after security (§4.9)
  and hands the negotiation leftover through the `ByteArray` argument
  (§4.7).
- The host (W5.6) serves the stream handlers through the `MuxSession`
  the chosen value returns, and joins its completion (§3.1).
- `cli/` (W5.8) and the interop matrix (W5.9) assemble the ordered
  muxer lists (§3.1). The W5.9 gate is `tcp + /noise + yamux` (root
  PLAN W5.9). The same-node-code-under-both payoff of PRINCIPLES 1.3
  was demonstrated in-process and over loopback; a live go matrix
  cannot exercise mplex against v0.50 and later.

## Test milestones (unit 1)

- `Mux.yamux` type-checks against the frozen seam of W5.2 with the
  session of W4.3, with no edit to `core` (the core pair, plan).
- `open` over a sim `Connection`, in both roles, returns a working
  `MuxSession`: the test opens a stream, echoes a payload, and closes
  (PRINCIPLES 1.4).
- The leftover `ByteArray` reaches the session as its first `Event`:
  the "negotiation" over-reads one byte, and the byte arrives at the
  stream layer (§4.7).
- The id constant carries the wire string:
  `Mux.yamuxId.toString = "/yamux/1.0.0"`, as a `#guard` the build
  checks (§3.4).
- The error path maps once: a hostile frame tears the session down,
  and the completion reports `Core.Error.protocol` through the single
  `Except.mapError` (§3.5).
- The fixed-ids test value serves a suite above, kept honest: a demo
  registry dials itself over the sim pair and serves one handler
  through the test session (§3.1).
- The suite passes under `+RTS -N1` (§6, PRINCIPLES 5.3).

## Test milestones (unit 2)

- The identity rule (§4.9): two sessions over a sim pair each number
  their streams from zero, and the session keys by `(id, initiator)`,
  so the two id-0 streams coexist, one per initiator, and each session
  map holds `(0, initiator)` beside `(0, non-initiator)` with no
  cross-delivery. The flag bit routes every inbound message to the key
  it names.
- The 1 MiB cap: a declared length one over the cap is a protocol
  error, rejected before allocation (§5.1, PRINCIPLES 2.3).
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

## Vector stance

`VECTORS.lock` holds no muxer entry, and `Tests/vectors/` on the spike
branch holds no mplex or yamux file; no muxer wire transcript was
captured. The yamux session carries its own suite in `net/yamux`: the
fixed header bytes, the hostile frames, and the flow-control cases
(the yamux pair, plan). This package pins the seam adaptation: the sim
exchanges of unit 1 through `Mux.yamux` and the test value, and the
identity and half-close cases of unit 2 through `Mux.mplex`. The live
gate is the go-libp2p interop matrix at W5.9 over `tcp + /noise +
yamux` (root PLAN W5.9); the spike proved that path once, and W5.9
re-runs it against this implementation. The same-node-code-under-both
payoff of PRINCIPLES 1.3 was demonstrated in-process and over loopback,
and a live go matrix cannot exercise mplex against v0.50 and later.
