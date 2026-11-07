# leanp2p libp2p protocols: architecture

`libp2p/protocols` holds the application protocols the host serves:
identify with push, ping, the req/resp framework (`/eth2/.../ssz_sn`),
and gossipsub v1.1. Each protocol registers its handlers into the host
registry (§3.10) and owns the `ProtoMessage` instances for its wire
messages (§3.2, §4.5). The package is the top of the libp2p chain (§2).
The consensus target ends here: identify feeds peer metadata and
gossipsub peer scoring, and req/resp and gossipsub carry the consensus
traffic (§8). The spike reference is `Protocol/{Identify,Ping}.lean` and
the message tables of `Crypto/Messages.lean` (§10, row 17; the libp2p
group is §7, row 10). The spike has no req/resp or gossipsub code.

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Protocols.lean` | the root module; one import line per public submodule |
| `Libp2p/Protocols/Constants.lean` | the protocol ids and the caps: `/ipfs/id/1.0.0`, `/ipfs/id/push/1.0.0`, `/ipfs/ping/1.0.0`, the `/eth2/.../ssz_sn` pattern of §8, gossipsub's `/meshsub/1.1.0`, one message cap per protocol, and the protocol version that the identify responder writes; other modules read these values from this module and do not repeat the literals (§3.8, §3.4) |
| `Libp2p/Protocols/Identify.lean` | the `Identify` message with its `ProtoMessage` instance (§3.2), `Identify.Error`, the validate, the client that reads and validates one response, the push sender, and the handler values for identify and push |
| `Libp2p/Protocols/Ping.lean` | `Ping.Error`, the echo handler, and the initiator that sends 32 bytes and awaits the echo |
| `Libp2p/Protocols/Identity.lean` | the boundary to `libp2p/identity`: the parse of the `publicKey` field, the peer id derivation, and the key serialization, each over the `List Nat` byte model; the pure half and the tests call these |
| `Libp2p/Protocols/Mock/{Core,Host}.lean` | the mocks of the unmerged dependencies (RULES.md, "Working ahead of the tree"); the integration deletes them |
| `Libp2p/Protocols/ReqResp/Frame.lean` | the `/eth2/.../ssz_sn` framing, a uvarint length over a snappy-compressed chunk, as a `Codec` with a `LawfulCodec` instance (§3.2); the snappy call goes through the `codec/snappy` binding (root PLAN W6.2); the codec feeds the core |
| `Libp2p/Protocols/ReqResp/Core.lean` | the response-chunk state machine of §3.3: `State`, `Event`, `Action`, the error inductive, and the total `step`; the snappy decompression context carries across chunks, and the chunk count and the error/EOF distinction live in the state |
| `Libp2p/Protocols/ReqResp/Exchange.lean` | the client and handler seam over the loop: the client function, the handler value the registry stores, and the deadlines |
| `Libp2p/Protocols/Gossipsub/Rpc.lean` | the RPC message with its `ProtoMessage` instance (§3.2) |
| `Libp2p/Protocols/Gossipsub/Core.lean` | `State`, `Event`, `Action`, `ProtocolError`, and the total `step` that holds mesh, scoring, and heartbeat (§3.3) |
| `Libp2p/Protocols/Gossipsub/Node.lean` | the loop task over the core, and the publish and subscribe surface at the seam level |

All declarations live in the `Libp2p.Protocols` namespace tree, and the
root module re-exports the public submodules. The Gossipsub module lines
are the unit's own planning work (W6.4); the root fixes the shape, and
the unit fixes the split.

The spike's `Crypto/Messages.lean` maps here (§10, row 17). The identify
table lands in `Identify.lean`. The `NoiseHandshakePayload` table went
to `libp2p/security` beside the handshake it serves. The `Envelope` and
`PeerRecord` tables stay deferred (§8; §10, row 17). One protocol per
module line keeps the responsibility split of PRINCIPLES 1.2; this
package holds four protocols, and no module holds two. The echo demo of
§2's tree comment (`identify, ping, echo (demo)`) is not in this
package; §4.9 names no echo, so no module line covers it.

## Public surface

- **Identify.** `Identify.protocolId` and `Identify.pushId` are the
  `ProtocolId` constants (§3.4 names `Identify.protocolId` as the root
  example; the literals live only in `Constants.lean`).
  `Identify.validate` checks, in order: the size cap, the decode, the
  presence and parse of `publicKey`, the derived id when the caller
  supplies one, and every listen and observed address through
  `Multiformats.Multiaddr.ofBytes?`. The client (the spike's `requestR`
  shape) reads one response, validates it, and returns the metadata for
  the peerstore. The client reads one frame per stream and drops the
  bytes after it. Go merges up to 10 frames; this client reads one. Go
  splits a record that carries a signed peer record and passes 2 KiB
  into two frames, and caps one response at 8 KiB; this package writes
  one frame and caps at 64 KiB. The
  two handler values serve inbound streams and register under their
  ids. The responder builds the message from the host's identity,
  addresses, protocol list, observed address, and agent version, as the
  spike's `respond` does. `Identify.pushTo` announces the same record
  on the stream that the host opened under `pushId`, and then
  half-closes. The host calls the sender after the local address set or
  the local protocol set changes. Go's identify service skips a push
  when the snapshot did not change, merges pending pushes into one
  round, and skips a connection that already carries the current record
  (the spike's `vendor/go-libp2p/p2p/protocol/identify/id.go`, the
  `loop` and `sendPushes` functions). This package sends one record per
  call and starts no timer. A received push updates the peerstore
  through the host. The push stores the addresses. The
  peerstore surface of the host doc holds addresses only, so a push's
  protocols list has no store yet. Go's push handler stores both. A
  push frame must carry the public key. The spec says to ignore missing
  fields; this handler rejects the push: `push` runs `validate`, so a
  push with no `publicKey` field fails with `.missingKey`. A stream
  that ends before any byte returns `.ok ()` and leaves the peerstore
  unchanged; go clears the peer's protocols.
- **Ping.** `Ping.protocolId` is the constant. The handler echoes each
  32-byte payload until the stream closes (the spike's `handle`). The
  initiator sends 32 bytes, awaits the echo, and checks its length and
  bytes; the spike's `Ping.ping` is the shape. The initiator's echo
  read has no deadline, as in the spike. §5.4 requires a deadline only
  in the unauthenticated phase. A silent peer parks the initiator until
  the stream closes.
- **Req/resp.** The framing codec feeds the core. The client side dials
  a stream through the host, sends one request under the framing, and
  awaits the response chunks under a deadline. The handler side serves
  one request the same way. Both work on opaque payload bytes; the core
  holds the chunk state and the error/EOF distinction.
- **Gossipsub.** `publish` hands a topic and payload bytes to the node,
  and `subscribe` registers a delivery callback. Both sit at the seam
  over the loop; the mesh decisions live in the core, and no caller
  sees them.

The client sides live in this package because §2 bans protocol logic in
`cli/`. `Identify.client` replaces the spike's `Identify.request`
(`requestR` over a bare stream), which the spike's `Main.lean` calls.
Both spike programs call `Ping.ping`.

## Owned contracts and how the package keeps them

1. **Every length-prefixed read is capped before allocation** (§5.1).
   Ping has no length prefix. Its payload size is the spec's 32 bytes,
   and `awaitEcho` rejects a longer accumulator after the read.
   Identify's cap is inherited from the spike: 65536 bytes, and a zero
   length is a protocol error (the spike's `requestR`). The package
   keeps that number in `Constants.identifyCap`. Unit 2 fixes the
   req/resp uvarint maximum against the eth2 framing rules, and unit 3
   fixes the gossipsub RPC maximum against the go implementation's
   default, which the W6.4 gate checks. Each number lands in
   `Constants.lean`. An over-long length is a protocol error, and the
   message is never allocated.
2. **A protocol failure is distinct from a clean stream end** (§5.2;
   root PLAN W6.3's deliverable). The §3.5 rule governs: a package that
   holds several independent protocols owns one error inductive per
   protocol, each mapped into `Core.Error` at its own seam. This
   package holds four, so `Identify.Error`, `Ping.Error`, the req/resp
   error in `ReqResp/Core.lean`, and `ProtocolError` are mapped at
   their seam values. `Identify.Error` maps in `pushHandler` with
   `Except.mapError` and directly in `writeRecord`. A framing failure is
   `Except E`. A peer that finished its half of the exchange is `none`;
   `Ping.ping` is the exception: a stream end before the echo is
   `.truncated`, because the exchange did not finish.
   No function reports both through one `Option`.
3. **Req/resp exchanges run under deadlines** (root PLAN W6.3). The
   mechanism is `withinDeadline` (§5.4). A response in flight fails at
   its deadline. An idle connection between exchanges never expires,
   per §5.4's scope rule.
4. **Identify and ping take no `step`** (§3.3, last rule). Identify has
   a pure codec and a pure `validate`. Ping has the pure `checkEcho`
   and no codec. `Identify.client` reads and validates one frame,
   `Identify.respondTo` and `Identify.pushTo` write one record, and the
   ping handler echoes until the stream closes.
5. **The gossipsub router is one pure `step` with time as an
   `Event.tick`** (§3.3; root PLAN W6.4). Mesh, scoring, and heartbeat
   hold in the same `State`, and every timer fires as an event. The
   yamux pair shows the shape. A test replays the core with no clock
   and no task. Each unbounded IO loop in the package, the gossipsub
   loop, the ping echo, the ping initiator's wait, the identify frame
   read, and the response-chunk loop, is a `partial def` with its reason
   in its module doc.
6. **Signing policies are a recorded decision** (root
   PLAN W6.4 names the space). The vendored pubsub spec fixes two axes,
   signature creation and signature verification. Unit 3 records the
   choice against the spec's options. The chosen policy must pass the
   go and rust interop tests of the W6.4 gate.
7. **SSZ stays client-side** (§8). The package frames opaque payload
   bytes and never encodes or decodes SSZ. A consumer project brings
   the payload types.

## Decisions

- **Identify and ping port the spike's tests and bytes** (§7). The
  identify suite replays the captured go transcript; the ping suite
  carries the 32-byte echo tests. The code shape comes from §3.3's
  last rule. The spike modules supply only the tests and the bytes.
- **Req/resp and gossipsub are new work with no spike reference**
  (§8 lists both as new). Unit 2 designs the framing and the
  response-chunk core from §3.3 and the eth2 framing rules the root
  records: uvarint length, snappy, and client-side SSZ. Unit 3 designs
  the router from §3.3 and the vendored gossipsub spec. The W6.4 gate
  runs the interop suite against go and rust and requires no behavior
  difference. It replaces conformance vectors, which do not exist for
  these protocols.
- **Snappy arrives only through the binding of root PLAN W6.2**
  (§4 preamble: FFI first). The owner decided the home:
  `codec/snappy`, a standalone binding package in the codec group.
  The binding wraps upstream `google/snappy`, which is C++; the C++
  runtime compiles out, the `LeanHazmatBn254` pattern. The binding
  exposes the block format only, raw `compress` and `decompress`; the
  length prefix stays in this package's framing. No module of this
  package names the foreign library.

## What the package must not depend on

- Nothing above it (§2). `cli/` is a consumer: W5.8 wires identify and
  ping into the demo node, and the consensus client of §8 consumes
  req/resp and gossipsub through this surface.
- Inside libp2p, the §2 chain gives it the host and everything below:
  the registry of §3.10 to register into, the peerstore to update on
  push, `ProtocolId` and the seam types from `core`.
- `base/conc` for the machinery the units need: `Async` for every
  signature that can park, `Chan` with a capacity and `select` for
  the gossipsub queues (root PLAN W6.4 names W1.1), `withinDeadline`
  for the req/resp deadlines, and `TaskSet` for the loop tasks.
- No SSZ anywhere. The package frames opaque bytes (§8).
- No snappy by name. The compression call goes through the
  `codec/snappy` binding interface, so a native Lean
  replacement can land behind the same interface (§4 preamble).
