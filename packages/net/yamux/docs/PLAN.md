# leanp2p yamux: plan

This plan refines the root `docs/PLAN.md` for `net/yamux`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Units 1a and 1b below together are the root unit W4.3. Of the
root row's dependency on W4.1, unit 1a needs nothing; it needs only
W1.2, because the header codec is pure over the byte model. Unit 1b
needs W4.1. The done-when of the pair is the root row plus
the root definition of done: the surface follows ARCHITECTURE §4.8 and
§7 row 9, the owned contracts hold, the carried tests pass, the suite
passes under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W1.2 | the header codec, the closed sets, and their theorems, all pure (root W4.3, first half) | the `LawfulCodec Header` law holds, the fixed spec bytes match, and the `ByteArray` path is pinned |
| 1b | W4.1, 1a | the core, the loop, and the session (root W4.3, second half) | the root W4.3 row holds, and the unit 1b milestones below pass |

The split exists because 1a is pure: with W1.2 in place it finishes
against frozen types, with no task, no channel, and no network. 1b
carries the W4.1 dependency, the concurrency, and the sim tests. W4.3
is done when both are done.

Units 0, 1a, and 1b are done: the suite is
`Tests/Yamux.lean`, and the theorems live in `Yamux/Header.lean`
(the round trip) and `Yamux/Invariants.lean` (the core invariants).

## Consumers

- `libp2p/mux` (W5.4) wraps the session as the yamux `Muxer` value and
  assigns it the `/yamux/1.0.0` id.
- The interop matrix (W5.9) dials go-libp2p over this session, on
  `tcp + /noise + yamux`, in both dial directions.
- The hostile-frame regressions are the interop prereqs of §7 row 9:
  W5.9 inherits them, and they stay permanent (PRINCIPLES 5.4).

## Test milestones (unit 1a)

- Fixed 12-byte encodings from the spec field table, the unit vectors
  of the spike suite: a data frame on stream 5 with length 3, a
  window-update SYN on stream 7 with the 256 KiB window, a ping SYN
  with opaque 42, a GoAway with code 0, and a data frame with FIN on
  stream 3.
- The round-trip law of `LawfulCodec Header` over the model, plus
  suffix consumption: a header decodes off the front of a longer
  buffer, and the rest comes back untouched (§6, layer 1).
- A prefix shorter than 12 bytes reports `truncated`.
- The `ByteArray` path is pinned to the model through the generic
  harness of `base/bytes`.

## Test milestones (unit 1b)

- Core invariants: the window theorem, the parity theorem, the
  retired-id theorem for our ids, the retired-key theorem for every
  stream, and the no-drop theorem for the receive path are
  build-checked statements over `step` (§6, layer 1).
- Transcript tests: no captured go-libp2p yamux transcript exists (see
  the vector stance). The conformance evidence is the spec-frame
  table, the hostile-frame suite, and the go-libp2p interop matrix at
  W5.9, where real go frames cross this session on the wire.
- Hostile frames (PRINCIPLES 5.4; §6, layer 4): a data frame beyond
  the receive window is a protocol error, the session tears down, and
  nothing is buffered. A SYN with the wrong parity creates no stream.
  A frame for an unknown id creates no state, and a later
  `openStream` of that id still works. A GoAway with each code ends
  the session. A ping flood leaves the control queue at its cap.
- Flow control: a writer parked on zero credit wakes on a window
  update. A writer that uses part of a grant hands the wake token to
  the next parked writer. The receive window never goes negative, as
  theorem and as observed behavior.
- Half-close (§5.3): close ends the write direction only, and the
  response after our FIN still arrives. PRINCIPLES 2.2 sets the
  discipline: the test asserts the spec, and it carries the case the
  spike's old test missed.
- Retirement: a stream both sides closed leaves the session map. The
  peer may open the id again; the new stream answers with its ACK, and
  an event of the old stream's handle reaches nothing.
- The accept queue: a stream that finds it full gets its ACK, then the
  RST.
- The write deadline: a peer that stops reading ends the session with
  `timeExpired`.
- Both units pass under `+RTS -N1`, the starvation criterion of §6.

## Vector stance

`VECTORS.lock` holds no yamux entry, and `Tests/vectors/` on the spike
branch holds no yamux file. No go-libp2p yamux transcript was
captured. What the spike holds instead: fixed header bytes derived
from the spec field table, the header round-trip theorem, session
exchanges over the byte-splitting sim transport, and the hostile-frame
cases of `Tests/Yamux.lean`. Those carry over as the suite of §7 row
9, and the spec-frame tests cover the header codec. The `spike` branch
is not on the remote, so the suite on `main` derives each check from
the vendored spec (`vendor/specs/yamux/README.md`) and from the
milestones above, and the fixed header bytes come from the spec field
table.

The go-libp2p interop matrix is the gate of W5.9; it runs after this
unit lands. Before it, `scripts/yamux-interop.sh` runs this session
against go-yamux v5.1.0 alone (the version go-libp2p v0.50 pins, with
go-libp2p's configuration), over plain loopback TCP, in both dial
directions: four concurrent streams of 1 MiB + 7 bytes each way, a
half-close before each echo, and a ping. Each listener checks that it
accepted exactly four streams and echoed each one, and exits with an
error otherwise. The Lean side is the
`yamux-interop` executable (`Tests/Interop/Yamux.lean`), outside
`lake test`, so the suite needs no Go. The spike proved the live path once (`tcp × noise ×
yamux`, lean ↔ go-libp2p, both dial directions). W5.9 re-runs that
matrix against this implementation.
