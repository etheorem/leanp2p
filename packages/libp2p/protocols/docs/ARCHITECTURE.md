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
| `Libp2p/Protocols/Constants.lean` | the protocol ids and the caps: `/ipfs/id/1.0.0`, `/ipfs/id/push/1.0.0`, `/ipfs/ping/1.0.0`, the `/eth2/.../ssz_sn` pattern of §8, gossipsub's `/meshsub/1.1.0`, and one message cap per protocol; one home per fact (§3.8, §3.4) |
| `Libp2p/Protocols/Identify.lean` | the `Identify` message with its `ProtoMessage` instance (§3.2), `Identify.Error`, the validate, the client that reads and validates one response, and the handler values for identify and push |
| `Libp2p/Protocols/Ping.lean` | `Ping.Error`, the echo handler, and the initiator that sends 32 bytes and awaits the echo |
| `Libp2p/Protocols/ReqResp/Frame.lean` | the `/eth2/.../ssz_sn` framing, a uvarint length over a snappy-compressed chunk, as a `Codec` with a `LawfulCodec` instance (§3.2); the snappy call goes through the binding of root PLAN W6.2, package TBD; the codec feeds the core |
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
§2's tree comment (`identify, ping, echo (demo)`) lands here as the
example handler value the demo node registers. §4.9 names no echo, so
it takes no module line and lives with the test support.

## Public surface

- **Identify.** `Identify.protocolId` and `Identify.pushId` are the
  `ProtocolId` constants (§3.4 names `Identify.protocolId` as the root
  example; the literals live only in `Constants.lean`).
  `Identify.validate` checks a received message: the peer id derived
  from the `publicKey` field matches the connected peer, and the size
  stays under the cap. The client (the spike's `requestR` shape) reads
  one response, validates it, and returns the metadata for the
  peerstore. The two handler values serve inbound streams and register
  under their ids. The responder builds the message from the host's
  identity, addresses, protocol list, observed address, and agent
  version, as the spike's `respond` does. The push sender sends the
  message under `Identify.pushId` (root W5.7 is "identify (+ push)"),
  and a push updates the peerstore through the host.
- **Ping.** `Ping.protocolId` is the constant. The handler echoes each
  32-byte payload until the stream closes (the spike's `handle`). The
  initiator sends 32 bytes, awaits the echo, and checks the length;
  the spike's `Ping.ping` is the shape.
- **Req/resp.** The framing codec feeds the core. The client side dials
  a stream through the host, sends one request under the framing, and
  awaits the response chunks under a deadline. The handler side serves
  one request the same way. Both work on opaque payload bytes; the core
  holds the chunk state and the error/EOF distinction.
- **Gossipsub.** `publish` hands a topic and payload bytes to the node,
  and `subscribe` registers a delivery callback. Both sit at the seam
  over the loop; the mesh decisions live in the core, and no caller
  sees them.

The client sides live in this package. §2 bans protocol logic in
`cli/`, and the spike's `Main.lean` and `PingNode.lean` call exactly
these: `Identify.request` (`requestR` over a bare stream), `Ping.ping`,
and the echo demo handler.

## Owned contracts and how the package keeps them

1. **Every length-prefixed read is capped before allocation** (§5.1).
   Ping's cap is the spec's fixed 32 bytes. Identify's cap is inherited
   from the spike: 65536 bytes, and a zero length is a protocol error
   (the spike's `requestR`). Unit 1 inherits the number, or records a
   change with a reason. Unit 2 fixes the req/resp uvarint maximum
   against the eth2 framing rules, and unit 3 fixes the gossipsub RPC
   maximum against the go implementation's default, which the W6.4 gate
   checks. Each number lands in `Constants.lean`. An over-long length
   is a protocol error, and the message is never allocated.
2. **A protocol failure is distinct from a clean stream end** (§5.2;
   root PLAN W6.3's deliverable). The §3.5 rule governs: a package that
   holds several independent protocols owns one error inductive per
   protocol, each mapped into `Core.Error` at its own seam. This
   package holds four, so `Identify.Error`, `Ping.Error`, the req/resp
   error in `ReqResp/Core.lean`, and `ProtocolError` each map once, at
   its own seam value, with `Except.mapError`. A framing failure is
   `Except E`. A peer that finished its half of the exchange is `none`.
   No function reports both through one `Option`.
3. **Req/resp exchanges run under deadlines** (root PLAN W6.3). The
   mechanism is `withinDeadline` (§5.4). A response in flight fails at
   its deadline. An idle connection between exchanges never expires,
   per §5.4's scope rule.
4. **Identify and ping take no `step`** (§3.3, last rule). Each has a
   pure codec, a pure `validate`, and a short IO function that reads
   one message, validates it, and answers.
5. **The gossipsub router is one pure `step` with time as an
   `Event.tick`** (§3.3; root PLAN W6.4). Mesh, scoring, and heartbeat
   hold in the same `State`, and every timer fires as an event. The
   yamux pair shows the shape. A test replays the core with no clock
   and no task. Each unbounded IO loop in the package, the gossipsub
   loop, the ping echo, and the response-chunk loop, is a `partial def`
   with its reason in its module doc.
6. **Signing policies are a recorded decision** (root
   PLAN W6.4 names the space). The vendored pubsub spec fixes two axes,
   signature creation and signature verification. Unit 3 records the
   choice against the spec's options; the go and rust interop of the
   W6.4 gate is the constraint that keeps the choice honest.
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
  the router from §3.3 and the vendored gossipsub spec. The W6.4 gate,
  the interop suite against go and rust with no behavior difference,
  closes conformance where no vectors exist.
- **Snappy arrives only through the binding of root PLAN W6.2**
  (§4 preamble: FFI first). The binding's package is not decided; the
  root row names no package, and this doc says "package TBD" until the
  owner records the home. No module of this package names a C library.

## What the package must not depend on

- Nothing above it (§2). `cli/` is a consumer: W5.8 wires identify and
  ping into the demo node, and the consensus client of §8 consumes
  req/resp and gossipsub through this surface.
- Inside libp2p, the §2 chain gives it the host and everything below:
  the registry of §3.10 to register into, the peerstore to update on
  push, `ProtocolId` and the seam types from `core`.
- `base/conc` for the machinery the units need: `Chan` with a capacity
  and `select` for the gossipsub queues (root PLAN W6.4 names W1.1),
  `withinDeadline` for the req/resp deadlines, and `TaskSet` for the
  loop tasks.
- No SSZ anywhere. The package frames opaque bytes (§8).
- No snappy by name. The compression call goes through the W6.2
  binding interface, wherever the owner places it, so a native Lean
  replacement can land behind the same interface (§4 preamble).
