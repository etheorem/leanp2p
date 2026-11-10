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
| 2a | W6.2 | the `/eth2/.../ssz_snappy` framing: CRC-32C, the snappy chunk codec as a `LawfulCodec` over the model pinned to the `ByteArray` path, and the protobuf varint length prefix with its round-trip theorem (root W6.3, first half) | the framing milestones pass at the model level |
| 2b | 2a, W5.6 | the reader core, `State`, `Event`, `Action`, and a total `step` for the request and the response chunks, plus the exchange: requester, responder, handler, deadlines, the caps, and the `MAX_CONCURRENT_REQUESTS` limit (root W6.3, second half) | the root W6.3 row holds, and the unit 2 milestones pass |
| 3a | W5.7 | the gossipsub RPC message with its instance, and the router core skeleton: `State`, `Event`, `Action`, a total `step` (root W6.4, first half) | the RPC milestones pass |
| 3b | 3a, W1.1 | mesh, scoring, and heartbeat inside the `step`; the signing-policy decision recorded; the loop and the publish/subscribe surface (root W6.4, second half) | the router milestones pass |
| 3c | 3b, W5.6 | the gate: the gossipsub interop suite against go and rust with no behavior difference (root W6.4's gate) | the gate passes, and the root W6.4 row holds |

Unit 0 is done.

The splits follow the deliverable size. Unit 2a is pure codec work that
starts when the snappy binding exists, and unit 2b needs the host's
streams for the core's loop and the exchange, so the two wait on
different things. Unit 3a is codec plus scaffolding, unit 3b is the
protocol body and the largest single deliverable, and unit 3c runs
against foreign nodes, so it carries its own milestone. The owner
decided the W6.2 home: `codec/snappy`, a standalone binding package
in the codec group wrapping upstream `google/snappy`.

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
- The push sender announces the local record and the receiver stores
  it: `Identify.pushTo` writes one frame on the push stream, the push
  handler on the other end validates it, and `addrsOf` reads the
  addresses back.
- The ping handler echoes 32 bytes and repeats until the stream closes.
  The concurrent-ping legs of the spike's 1000-stream stress stay as
  the load check.
- The ping initiator rejects a wrong length: the spike's `Ping.ping`
  sends 32 bytes, awaits the echo, and fails on any other size. A
  stream that ends before one whole payload arrives is a protocol error
  (§5.2).
- The suite passes under `+RTS -N1`.

## Test milestones (unit 2)

- The checksum: CRC-32C gives the four examples of RFC 3720, appendix
  B.4, on the model and on the table path, and the two paths agree.
- The chunk codec round-trips on the model with the `LawfulCodec`
  instance, and the `ByteArray` read agrees with the model.
- The length prefix round-trips for every `Uint64` value (a theorem),
  takes a non-minimal prefix, and refuses 11 bytes and `2 ^ 64`.
- Transcript tests replay requests and responses with no clock and no
  task: a payload split across snappy chunks, read whole, in pieces,
  and one byte at a time, gives the same chunks (§3.3). The output so
  far and the budget spent carry from chunk to chunk.
- The framing rules, one rejection each: a chunk before the stream
  identifier, a wrong identifier, an unskippable chunk, a wrong
  checksum, a short data chunk, a data chunk over 65536 bytes, a broken
  block, and data past `n`. Padding, the skippable range, and a
  repeated identifier are skipped.
- The go fixtures: payloads that go's snappy writes at prysm's pin read
  back, as a request and as a response chunk, and the empty payload is
  the prefix alone.
- The writer: with a block that shrinks, it writes compressed chunks,
  and they read back, alone and beside a raw chunk. A block that does
  not shrink, or a compressor error, gives a raw chunk.
- The concurrency limit: two requests with one id take a slot each, a
  third is refused, another id has its own slots, and a request gives
  its slot back when it ends (the bound of `Table.take` is a theorem).
- Between two hosts over the sim transport, with Noise and yamux
  (PRINCIPLES 1.4):
  - a request through the host gets its chunks, with whole and with
    split writes;
  - an id the peer does not serve fails the open, since
    multistream-select answers `na`;
  - a silent peer fails the request at its deadline;
  - a connection closed under a parked read ends the request.
- The error/EOF distinction: a framing failure returns the protocol
  error, and a clean stream end returns `finished`, through different
  channels (§5.2). An end inside a chunk is an early EOF.
- The response: context bytes on success, none on an error chunk; an
  error chunk ends the response; the reader stops at `maxChunks`.
- The deadline: a silent responder fails the request at its deadline,
  and a silent requester fails the responder's read. The test `Clock`
  of `base/conc` advances both, so the suite waits on no wall clock.
- The caps: a length outside the method's bounds or past
  `MAX_PAYLOAD_SIZE` is refused, an error message over 256 bytes is
  refused, and a chunk header past `max_compressed_len(n)` is refused
  before its body arrives (§5.1).
- SSZ payloads pass through as opaque bytes: a payload of arbitrary
  bytes survives the framing unchanged, and no module inspects it.
- The suite passes under `+RTS -N1`.

## Test milestones (unit 3)

- The RPC codec against the spec's canonical examples: the repo carries
  none, so the codec family closes with fixed-message tests from the
  field tables of the vendored gossipsub spec, both directions.
- The router core as transcript tests, `Event.tick` advancing the
  heartbeat: mesh graft and prune transitions, and iwant/ihave
  bookkeeping (root PLAN W6.4).
- The signing-policy tests, once unit 3b records the choice against the
  two axes of the pubsub spec.
- Unit 3b owns the trickle regressions that issue #23's done-when names.
  Tests/Gossipsub/Node.lean pins the IHAVE deadlines on a test clock.
  The checks cover configured delays across heartbeats and the default
  zero-delay schedule.
- The loop suite, `Tests/Gossipsub/Node.lean`, runs over the in-memory
  switch of `Tests/Gossipsub/Switch.lean`, a double of the real
  `Libp2p.Core` handler seam:
  - One publish crosses two nodes and reaches the callback.
  - Subscribe registers the callback before posting its event. A refused
    post takes back its own registration by id.
  - A subscribe after the join reaches the peer, and an unsubscribe sends
    the negative record.
  - A bad frame fails its handler and resets its stream. A body that does
    not decode leaves the loop running.
  - The handler serves every frame of a stream, in any chunking, and resets
    the stream on a bad frame.
  - Each peer has a writer task and a 32-slot queue. Two publishers run in
    parallel with one stream each and zero adjacent inversions per peer.
    A full queue drops frames, and the suite reports the drop count.
  - A parked peer writer leaves the loop free. Stop resets its stream,
    closes the peer queues and alarm, and joins the owned tasks.
  - The handler registers its opener before the first RPC. Repeat joins
    emit no hello. Subscription records precede grafts.
  - The replayable hash order changes across heartbeat counters.
  - Pending gossip holds at most 256 sends. Excess sends increment the
    drop count. Due sends leave before the heartbeat shifts the cache.
  - The receipt observer sees duplicates before validation and delivery.
  - The default gossip delay is zero. Tests supply an explicit spread.
  - A heartbeat sends the graft, and a later publish reaches the mesh.
  - With a configured spread, each IHAVE leaves at its run-wide indexed
    delay and no earlier. The check crosses two heartbeat intervals.
  - A publish with no peers opens no stream and delivers nothing locally.
  - `stop` joins the loop, a later post answers `false`, and the switch
    closes.
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
- **Req/resp has fixtures and no vector file.** The spike captured no
  eth2 traffic, and the consensus spec tests carry no req/resp case:
  their `networking` format covers gossip validation and the
  custody-group functions (`tests/formats/networking` of
  consensus-specs).
  `scripts/reqresp-fixtures` writes `Tests/fixtures/reqresp-snappy-go.json`
  with go's snappy at the version prysm's `go.mod` pins, in the shape of
  prysm's `EncodeWithMaxLength` (both vendored under `vendor/prysm`).
  RFC 3720, appendix B.4, gives the checksum examples. The spec texts
  are vendored under `vendor/consensus-specs` and `vendor/snappy`. The
  framing family closes with these, the
  round-trip proofs, the pin to the byte model, and the fixed-message
  tests of unit 2.
- **Gossipsub has no vectors.** The vendored gossipsub spec carries no
  captured examples. Fixed-message tests close the RPC codec family.
  The W6.4 gate is a live interop suite against go and rust; no vector
  file covers it.
