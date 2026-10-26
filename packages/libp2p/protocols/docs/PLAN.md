# leanp2p libp2p protocols: plan

This plan refines the root `docs/PLAN.md` for `libp2p/protocols`. The
package carries three root units: W5.7 (identify and ping), W6.3 (the
req/resp framework), and W6.4 (gossipsub v1.1). The done-when of each
is the root row plus the root definition of done: the surface follows
ARCHITECTURE §4.9, shaped by §3, the owned contracts hold, the carried
tests pass, the suite passes under `+RTS -N1`, and the import lint is
green. This is the largest plan of the stage, so units 2 and 3 are
sub-split below, with the reasons.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W5.6 | identify (+ push) and ping: the message and its `ProtoMessage` instance, the validate, the handlers, and `Constants.lean` (root W5.7) | the root W5.7 row holds, and the unit 1 milestones pass |
| 2a | W6.2 | the `/eth2/.../ssz_sn` framing codec: uvarint length over a snappy chunk, as a `LawfulCodec` over the model, pinned to the `ByteArray` path (root W6.3, first half) | the framing milestones pass at the model level |
| 2b | 2a, W5.6 | the response-chunk core, `State`, `Event`, `Action`, the error inductive, and a total `step`, plus the exchange: client, handler, deadlines, and the caps (root W6.3, second half) | the root W6.3 row holds, and the unit 2 milestones pass |
| 3a | W5.7 | the gossipsub RPC message with its instance, and the router core skeleton: `State`, `Event`, `Action`, a total `step` (root W6.4, first half) | the RPC milestones pass |
| 3b | 3a, W1.1 | mesh, scoring, and heartbeat inside the `step`; the signing-policy decision recorded; the loop and the publish/subscribe surface (root W6.4, second half) | the router milestones pass |
| 3c | 3b, W5.6 | the gate: the gossipsub interop suite against go and rust with no behavior difference (root W6.4's gate) | the gate passes, and the root W6.4 row holds |

Unit 0 is done.

The splits follow the deliverable size. Unit 2a is pure codec work that
starts when the snappy binding exists, and unit 2b needs the host's
streams for the core's loop and the exchange, so the two wait on
different things. Unit 3a is codec plus scaffolding, unit 3b is the
protocol body and the largest single deliverable, and unit 3c runs
against foreign nodes, so it carries its own milestone. W6.2 names no
package (the open question on record); this plan refers to it as
package TBD, per the owner's decision.

## Consumers

- `cli/` (W5.8) wires identify and ping into the demo node and the ping
  node (root PLAN W5.8; the spike's `Main.lean` and `PingNode.lean`
  show the wiring).
- The consensus client consumes req/resp and gossipsub through the
  handler values and the client side (§8). SSZ payload types stay with
  the client.
- The W5.9 matrix covers this package's identify and ping over a real
  node: the spike's node suite pings and identifies between two Lean
  hosts over loopback TCP, `scripts/ping-interop.sh` pings a go node both ways
  on loopback, and identify against go closes through the captured
  vector.

## Test milestones (unit 1)

- The captured identify transcript replays: `Tests/vectors/identify-go.json`
  on the spike branch, a captured go-libp2p Identify protobuf, arriving
  through W0.3.
- `Identify.validate` rejects a message whose derived peer id mismatches
  the connected peer, and a message over the cap.
- A push through the push handler updates the peerstore through the
  host, and the entry reads back.
- The ping handler echoes 32 bytes and repeats until the stream closes.
  The concurrent-ping legs of the spike's 1000-stream stress stay as
  the load check.
- The ping initiator rejects a wrong length: the spike's `Ping.ping`
  sends 32 bytes, awaits the echo, and fails on any other size. A
  partial payload at EOF is a protocol error, a recorded delta from the
  spike's responder, which closes silently (§5.2).
- The suite passes under `+RTS -N1`.

## Test milestones (unit 2)

- A request and its response round-trip through uvarint + snappy at the
  model level, with the `LawfulCodec` instance, once the binding exists.
- Transcript tests replay chunked responses with no clock and no task:
  a response split across snappy chunks drives the core, and the
  decompression context carries across chunks (§3.3).
- The error/EOF distinction: a framing failure returns the protocol
  error, and a clean stream end returns `none`, through different
  channels (§5.2).
- The deadline: a slow response fails at its deadline, and the test
  `Clock` of `base/conc` advances it, so the suite waits on no wall
  clock.
- The caps: an over-long uvarint length is a protocol error, and no
  allocation of that size happens (§5.1).
- SSZ payloads pass through as opaque bytes: a payload of arbitrary
  bytes survives the framing unchanged, and no module inspects it.
- The suite passes under `+RTS -N1`.

## Test milestones (unit 3)

- The RPC codec against the spec's canonical examples: the repo carries
  none, so the codec family closes with fixed-message tests from the
  field tables of the vendored gossipsub spec, both directions.
- The router core as transcript tests, `Event.tick` advancing the
  heartbeat: mesh graft and prune transitions, and iwant/ihave
  bookkeeping, at the level the root names (root PLAN W6.4).
- The signing-policy tests, once unit 3b records the choice against the
  two axes of the pubsub spec.
- The gate (unit 3c): the interop suite against go and rust runs with
  no behavior difference, per root PLAN W6.4. This is a live suite over
  foreign nodes, and it closes the unit where no vector file can.
- The suite passes under `+RTS -N1`.

## Vector stance

- **Identify has a vector.** The spike pins
  `Tests/vectors/identify-go.json`, a captured go-libp2p Identify
  protobuf. W0.3 moves the spike's `Tests/vectors/` directory to main,
  and unit 1 replays it.
- **Ping has no vector file.** The ping spec fixes the id and the
  32-byte size, so it carries no message vectors. The spike validates
  ping by behavior tests over the sim plus a live go interop script
  (`scripts/ping-interop.sh` on the spike branch). The behavior tests
  close the family.
- **Req/resp has no vectors, and none are scheduled.** W0.3 carries the
  spike's directory only, and the spike captured no eth2 traffic. The
  framing family closes with the round-trip proof, the fuzz pin to the
  byte model, and the fixed-message tests of unit 2.
- **Gossipsub has no vectors.** The vendored gossipsub spec carries no
  captured examples. Fixed-message tests close the RPC codec family.
  The W6.4 gate is a live interop suite against go and rust; no vector
  file covers it.
