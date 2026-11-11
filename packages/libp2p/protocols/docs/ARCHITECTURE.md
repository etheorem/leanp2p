# leanp2p libp2p protocols: architecture

`libp2p/protocols` holds the application protocols the host serves:
identify with push, ping, the req/resp framework (`/eth2/.../ssz_snappy`),
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
| `Libp2p/Protocols/Constants.lean` | the protocol ids and the caps: `/ipfs/id/1.0.0`, `/ipfs/id/push/1.0.0`, `/ipfs/ping/1.0.0`, the `/eth2/beacon_chain/req/<name>/<version>/ssz_snappy` pattern of §8, gossipsub's `/meshsub/1.1.0`, one message cap per protocol, and the protocol version that the identify responder writes; for req/resp also `MAX_PAYLOAD_SIZE`, `max_compressed_len`, the result codes, and the constants of the snappy framing format; one home per fact (§3.8, §3.4) |
| `Libp2p/Protocols/Identify.lean` | the `Identify` message with its `ProtoMessage` instance (§3.2), `Identify.Error`, the validate, the client that reads and validates one response, the push sender, and the handler values for identify and push |
| `Libp2p/Protocols/Ping.lean` | `Ping.Error`, the echo handler, and the initiator that sends 32 bytes and awaits the echo |
| `Libp2p/Protocols/Identity.lean` | the boundary to `libp2p/identity`: the parse of the `publicKey` field, the peer id derivation, and the key serialization, each over the `List Nat` byte model; the pure half and the tests call these |
| `Libp2p/Protocols/ReqResp/Crc32c.lean` | CRC-32C (RFC 3720) and the checksum mask of the snappy framing format: the bitwise model and the table path that runs |
| `Libp2p/Protocols/ReqResp/SnappyFrame.lean` | one chunk of the snappy framing format: the closed set of chunk types and the chunk codec, a `Codec` with a `LawfulCodec` instance (§3.2), plus the `ByteArray` header read the core runs |
| `Libp2p/Protocols/ReqResp/Payload.lean` | what both directions share: `ReqResp.Error`, the result codes, `Method` and the size bounds, the protobuf varint length prefix with its round-trip theorem, and the writer; the snappy call goes through the `codec/snappy` binding (root PLAN W6.2) |
| `Libp2p/Protocols/ReqResp/Core.lean` | the reader state machine of §3.3: `State`, `Event`, `Action`, and the total `step`; it reads one request or a run of response chunks, and the output so far, the budget spent, the chunk count, and the error/EOF distinction live in the state |
| `Libp2p/Protocols/ReqResp/Limiter.lean` | `MAX_CONCURRENT_REQUESTS`: the pure table rule with its bound theorem, and the per-peer `Limiter` over `OnceRef` |
| `Libp2p/Protocols/ReqResp/Exchange.lean` | the shell over the core: the requester `request` and `requestPeer`, the responder `serve`, the handler value the registry stores, and the deadlines |
| `Libp2p/Protocols/StreamError.lean` | `mapStreamError`, the one map from a stream error into `Core.Error` that the req/resp handler uses |
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
package holds four protocols, and no module holds two. §4.9 names
identify, ping, req/resp, and gossipsub, and the module list follows
that sentence. The package exports no echo handler. A contributor
working decision on the CLI branch places the future demo echo
handler and client at `Libp2p.Protocols.TestSupport.Echo`. The
protocol id is `/demo/echo/1.0.0`, in that one module, as a
`StreamHandler`. Test support sits beside the four protocols. The
review context is
https://github.com/etheorem/leanp2p/issues/22#issuecomment-6805941244.
This package does not implement that module yet.

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
  addresses, protocol list, and agent version, as the spike's `respond`
  does. The observed address is the `remoteAddr` of the stream's
  `StreamContext`, as go-libp2p reads it from `s.Conn()`
  (`vendor/go-libp2p/p2p/protocol/identify/id.go`). The push handler
  checks the pushed key against the context's `remotePeer`. `Identify.pushTo` announces the same record
  on the stream that the host opened under `pushId`, and then
  half-closes. The host calls the sender after the local address set or
  the local protocol set changes. Go's identify service skips a push
  when the snapshot did not change, merges pending pushes into one
  round, and skips a connection that already carries the current record
  (`vendor/go-libp2p/p2p/protocol/identify/id.go`, the `loop` and
  `sendPushes` functions). This package sends one record per
  call and starts no timer. A received push updates the peerstore
  through the host (`Host.addAddrs`). The push stores the addresses. The
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
- **Req/resp.** A `Method` names the protocol id, the size bounds of
  the request and of a success chunk, the width of the context bytes,
  and the most chunks the client reads. The client project declares its
  methods, since the bounds come from its SSZ types (§8). Opening the
  stream to the peer and negotiating the id is the host's job (W5.6),
  as go-libp2p's `NewStream` does it
  (`vendor/go-libp2p/p2p/host/basic/basic_host.go`, line 441). The host
  names it `newStream`. `requestPeer` takes the call as an argument, with a slot
  of the peer's `Limiter`, and runs `request` on the stream the call
  returns. `request` needs no host type: it writes
  the request, half-closes, and hands each response chunk to a callback
  under a deadline. `serve` reads one request, answers through a
  callback, and closes, and `handler` wraps it as the `StreamHandler`
  the registry stores. Both work on opaque payload bytes; the core holds
  the reader state and the error/EOF distinction.
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
   keeps that number in `Constants.identifyCap`. Req/resp takes its
   caps from the consensus spec ("SSZ-snappy encoding strategy"): the
   length prefix is at most 10 bytes; the length fits the bounds of the
   method and `MAX_PAYLOAD_SIZE`, whichever is smaller; an error chunk
   carries at most 256 bytes, the `ErrorMessage` limit; and the framed
   bytes after the prefix never pass `max_compressed_len(n)`. The
   reader checks the budget at each chunk header, before it buffers the
   body. Unit 3 fixes the gossipsub RPC maximum against the go
   implementation's default, which the W6.4 gate checks. Each number
   lands in `Constants.lean`. An over-long length is a protocol error,
   and the message is never allocated.
2. **A protocol failure is distinct from a clean stream end** (§5.2;
   root PLAN W6.3's deliverable). The §3.5 rule governs: a package that
   holds several independent protocols owns one error inductive per
   protocol, each mapped into `Core.Error` at its own seam. This
   package holds four, so `Identify.Error`, `Ping.Error`, the req/resp
   error in `ReqResp/Payload.lean`, and gossipsub's `ProtocolError`
   each map once, at its own seam value. `Identify.Error` maps in
   `pushHandler` with `Except.mapError` and directly in `writeRecord`.
   A framing failure is `Except E`. A peer that finished its half of
   the exchange is `none`; `Ping.ping` is the exception: a stream end
   before the echo is `.truncated`, because the exchange did not
   finish. No function reports both through one `Option`.
3. **Req/resp exchanges run under deadlines** (root PLAN W6.3). The
   mechanism is `withinDeadline` (§5.4). A response in flight fails at
   its deadline. The spec leaves the requester's timeout to the client
   ("a timeout on the request that depends on the nature of the
   request"), so each call takes the deadline as an argument and no
   constant holds it. The responder's deadline covers the read of the
   request only: a responder may withhold chunks to rate-limit, and it
   "MUST NOT respond with an error or close the stream when rate
   limiting". On expiry the shell resets the stream from a task it owns
   and joins. An idle connection between exchanges never expires, per
   §5.4's scope rule.
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
   read, and the req/resp read loop (`pump`), is a `partial def` with
   its reason in its module doc.
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
  (§8 lists both as new). Unit 2 takes the framing and the reader core
  from §3.3 and the consensus spec (`vendor/consensus-specs/specs/phase0/p2p-interface.md`
  and `vendor/consensus-specs/specs/altair/p2p-interface.md`): a
  protobuf varint length, the snappy framing format
  (`vendor/snappy/framing_format.txt`), and client-side SSZ. The
  client sources the decisions below cite are vendored too
  (`vendor/lighthouse`, `vendor/prysm`, `vendor/lodestar`, each with a
  narrow `paths` list in `VECTORS.lock`). Unit 3 designs
  the router from §3.3 and the vendored gossipsub spec. The W6.4 gate,
  the interop suite against go and rust with no behavior difference,
  closes conformance where no vectors exist.
- **Snappy arrives only through the binding of root PLAN W6.2**
  (§4 preamble: FFI first). The owner decided the home:
  `codec/snappy`, a standalone binding package in the codec group.
  The binding wraps upstream `google/snappy`, which is C++; the C++
  runtime compiles out, the `LeanHazmatBn254` pattern. The binding
  exposes the block format only, raw `compress` and `decompress`; the
  length prefix, the framing format, and its CRC-32C stay in this
  package's framing. No module of this package names the foreign
  library.
- **Req/resp uses the snappy framing format.** The spec says so
  ("snappy-framing is used", "Snappy frames compression"), and so do
  the clients: lighthouse reads through `snap::read::FrameDecoder`
  (`vendor/lighthouse/beacon_node/lighthouse_network/src/rpc/codec.rs`,
  line 187), and prysm writes through `snappy.NewBufferedWriter`
  (`vendor/prysm/beacon-chain/p2p/encoder/ssz.go`, lines 55 and 219).
  A framed stream has many spellings of one payload
  (compressed or raw chunks, padding, a repeated identifier), so the
  chunk codec carries the `LawfulCodec`, and the payload layer proves
  its length prefix. The suite reads the go fixtures, written at
  prysm's snappy pin, and pins each framing rule.
- **The length prefix accepts a non-minimal varint of at most 10
  bytes.** The spec makes minimality a SHOULD and the 10-byte limit a
  MUST ("It SHOULD be minimally encoded ... and MUST not exceed 10
  bytes"). The writer is minimal, and the reader takes what the MUST
  allows. Prysm reads the same way: `readVarint` takes up to 10 bytes,
  then `proto.DecodeVarint`
  (`vendor/prysm/beacon-chain/p2p/encoder/varint.go`, lines 16 and 41).
  The multiformats
  varint of `codec/varint` refuses both, so the payload layer has its
  own reader. The suite pins a non-minimal prefix, an 11-byte prefix,
  and a value of `2 ^ 64`.
- **A zero-length payload is the prefix alone.** Go's snappy writer
  writes no chunk for an empty input: the go fixture `empty` is the
  byte `00`. The reader of `n = 0` reads no chunk; lodestar's reader
  loops while it holds fewer than `n` bytes, so it reads none either
  (`vendor/lodestar/packages/reqresp/src/encodingStrategies/sszSnappy/decode.ts`,
  line 95). The suite checks that the writer gives the go bytes.
- **Every non-zero result carries an `ErrorMessage`.** The spec gives
  the schema for codes 1 to 3, makes the reserved range an error, and
  leaves the schema of codes 128 to 255 to each request. Lighthouse
  decodes the payload of every non-zero code as `ErrorType`, within
  its bounds (`decode_error`, `rpc/codec.rs` lines 300 to 312 of
  `vendor/lighthouse`), and maps every code it does not know to
  `Unknown` (`rpc/methods.rs`, line 784). The reader does the same: 256 bytes
  at most, and no context bytes (altair: "On a non-zero `<result>`
  with `ErrorMessage` payload, the `<context-bytes>` is also empty").
- **The requester stops at its last chunk.** It reads until the peer
  closes, an error chunk arrives, or `maxChunks` chunks arrived
  ("Requesting side", rules 1, 2, and 4). It reads no byte after that,
  and it resets the stream when the peer has not closed. So the answer
  does not depend on how the transport split the reads. The responder
  reads the request to the end of the stream and refuses a byte after
  it ("at which point an EOF should arise").
- **The size bounds come from the client.** The spec bounds each
  payload by its SSZ type ("within the expected size bounds derived
  from the payload SSZ type or `MAX_PAYLOAD_SIZE`, whichever is
  smaller"). The SSZ types stay with the client (§8), so a `Method`
  carries the bounds, as lodestar's reader takes `TypeSizes`
  (`sszSnappy/decode.ts` of `vendor/lodestar`, lines 33 and 69).
- **The requester keeps `MAX_CONCURRENT_REQUESTS`.** "The requester
  MUST NOT make more than `MAX_CONCURRENT_REQUESTS` concurrent requests
  with the same protocol ID" (phase0 "Requesting side"). `requestPeer`
  takes a slot of a `Limiter` per peer before it opens the stream and
  refuses a third request with `tooManyRequests`, since the spec
  forbids the request and a wait would park on another request's
  deadline. The slot goes back on every path. The responder's side of
  the rule, "MAY penalise", is scoring, and stays with the client.
- **The suite runs between two hosts over the sim.** `Tests/HostPair.lean`
  builds two real hosts on the test values of root §3.1: the sim
  transport, the fixed-key Noise value, and a test clock, with yamux. The
  requester opens its stream through the host's `newStream` (go-libp2p's
  `NewStream`, `vendor/go-libp2p/p2p/host/basic/basic_host.go`, line
  441). The responder registers through `setHandler`. A host failure
  that wraps a seam error reaches `requestPeer` as that error.

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
- From the codec group, `codec/varint` for the minimal LEB128 writer
  the length prefix shares, `codec/proto` for the little-endian
  digits of the chunk length and their lemmas (`Pb.leBytes`,
  `Pb.leOf`), so neither fact has a second home, and `codec/snappy`
  for the raw block `compress` and `decompress`.
- No SSZ anywhere. The package frames opaque bytes (§8).
- No snappy by name. The compression call goes through the
  `codec/snappy` binding interface, so a native Lean
  replacement can land behind the same interface (§4 preamble).
