# leanp2p libp2p negotiate: plan

This plan refines the root `docs/PLAN.md` for `libp2p/negotiate`. The
root plan owns the order across packages (PLAN.md, "How to read this
plan"). Units 1a and 1b below are the root unit W5.5, with root deps
W5.2, W5.3, and W5.4. The done-when of unit 1b is the root row plus the
root definition of done: the surface follows ARCHITECTURE §4.9, shaped
by §3, the owned contracts hold, the carried vector and property tests
pass, the suite passes under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W5.2 | the multistream core: `Constants.lean`, the `Msg` codec with its `LawfulCodec` instance and the `ls` framing, and `State`/`Event`/`Action`/`step` with the `Reply` set and `Negotiate.Error` | the core replays the transcript milestones below with no connection in the loop |
| 1b | 1a, W5.3, W5.4 | the upgrader: `Negotiate.upgrade` over the ordered seam lists, the identity check, the leftover hand-over between the three stages, the `Except.mapError` into `Core.Error`, the deadline wiring | the root W5.5 row holds, and the milestones below pass |

The split mirrors the security pair's: the pure side closes on
transcripts alone, and among the W5 units it needs only `ProtocolId`
from W5.2. W5.3 and W5.4 gate the seam calls and the end-to-end path of
unit 1b, so unit 1a can land while they finish.

Unit 0 is done.

## Consumers

- The host (W5.6) runs the upgrader inside its dial and accept paths,
  supplies the expected `PeerId` on the dial path, and matches on
  `Core.Error` (§3.5, §4.9).
- `cli/` (W5.8) assembles the ordered `SecurityProtocol` and `Muxer`
  lists and passes them down (§3.1).
- The interop matrix (W5.9) is the live gate: `tcp + /noise + yamux`,
  dial and listen (root PLAN W5.9). The path runs this package's
  negotiation twice, once for security and once for the muxer.

## Test milestones (unit 1a)

- The wire examples replay: `na` encodes to `03 6e 61 0a`, the header
  encodes to its recorded bytes, and both decode back (`mss-wire.json`).
- The `ls` framing: the request `03 6c 73 0a`, and the reply body for
  `/ipfs/kad/1.0.0` and `/ipfs/id/1.0.0` matches the recorded bytes of
  `mss-ls.json`. The reply decodes back to the two ids.
- The captured go traces replay through the core as events in and
  actions out, in both roles: the full exchange, the `na` exchange, and
  the lazy exchange of `mss-go-trace.json` (captured from go-libp2p
  v0.50.0 over go-multistream v0.6.1). The lazy trace pins the
  back-to-back header-plus-proposal write.
- The 1 KiB cap: a declared length one byte over the cap is rejected
  before any payload allocation, as a protocol error (§5.1,
  PRINCIPLES 2.3).
- The `DecodeError` terms (§3.2, §5.2): a short prefix stays
  incomplete, and more bytes may complete it; a message with no
  trailing `\n`, a bad UTF-8 body, or a varint that cannot complete
  within 9 bytes is malformed, and the reader stops waiting (§4.3).
- The round-trip harness of `base/bytes` runs over the `Msg` instance.

## Test milestones (unit 1b)

- The full pipeline over the sim transport, in both directions: dial
  and listen, negotiation → security → muxer, with the real
  `Noise.securityProtocol` value (or the fixed-key test value) and
  `Mux.yamux` (PRINCIPLES 1.4).
- The leftover hand-over at each stage boundary (§4.7, §5.6): a byte
  the negotiation over-reads reaches the handshake; a byte the
  handshake over-reads reaches the muxer negotiation; a byte the muxer
  negotiation over-reads reaches the session loop as its first `Event`.
- The `na` retry: a responder that answers `na` for the first muxer id
  receives the next proposal, and the negotiation lands on the second
  id of the dialer's list.
- The identity check (§4.9): a dial to a peer whose static key derives
  a different id fails with `Core.Error.authentication`, before any
  muxer byte moves.
- The 30 s deadline (§5.4): a peer that goes silent mid-upgrade fails
  the upgrade at the deadline, the teardown closes the connection, and
  the parked reads end on their own (PRINCIPLES 3.1), and the host
  joins every task of it (PRINCIPLES 3.2). The test `Clock` of
  `base/conc` advances the deadline, so the suite waits on no wall
  clock.
- The wire fallback: the handshake payloads carry no muxer
  advertisement, and the connection lands on yamux through the wire
  negotiation alone.
- The suite passes under `+RTS -N1` (§6, PRINCIPLES 5.3).

## Vector stance

The multistream traces exist on the spike branch and arrive through
W0.3 with `VECTORS.lock` (§6): `mss-wire.json` (the spec framing
examples), `mss-ls.json` (the `ls` request and reply framing from the
multistream README), and `mss-go-trace.json` (captured go-libp2p
v0.50.0 exchanges: full, `na`, and lazy). The upgrader milestones also
lean on the Noise and yamux transcript sets the security and yamux
pairs name, since the pipeline runs their values. W5.9 is the live
gate: the go-libp2p matrix over `tcp + /noise + yamux` exercises the
whole upgrade against a foreign peer and closes the unit for real.
