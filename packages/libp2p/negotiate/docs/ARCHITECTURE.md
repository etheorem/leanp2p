# leanp2p libp2p negotiate: architecture

`libp2p/negotiate` implements multistream-select 1.0.0 as a pure `step`
(§3.3) and the upgrader that walks a raw `Connection` through security
and muxer negotiation into a `MuxSession` (§4.9). It imports `core` and
no implementation of the seams (§2, §3.1); the ordered lists arrive as
configuration (§3.1). The spike's upgrader imported Noise and yamux to
name their types; this package removes that coupling (§9, delta 10).
The spike reference is `Protocol/Multiselect.lean` and
`Conn/Upgrade.lean` (§10 row 14).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Negotiate.lean` | the root module; one import line per public submodule |
| `Libp2p/Negotiate/Constants.lean` | `Negotiate.protocolId` (`/multistream/1.0.0`) and `Negotiate.maxMsg` (the 1 KiB cap of §5.1); one home per fact (§3.8) |
| `Libp2p/Negotiate/Message.lean` | the `Msg` type, its `Codec` and `LawfulCodec` instances (§3.2), the uvarint length prefix, the `ls` reply framing |
| `Libp2p/Negotiate/Step.lean` | the pure core: `State`/`Event`/`Action`/`step`, the `Reply` closed set, `Negotiate.Error` (§3.3, §3.4, §3.5) |
| `Libp2p/Negotiate/Upgrade.lean` | `Negotiate.upgrade`, the upgrader over the seam lists, the identity check, the deadline wiring |

All declarations live in the `Libp2p.Negotiate` namespace, and the root
module re-exports the public submodules. The 30 s upgrade deadline is
owned by `net/streams` and lives in `Streams/Constants.lean` (the
streams pair, contracts; the security pair, contract 7). This package
imports it and wires it; it keeps no copy.

## Public surface

- `Msg` is the multistream message: one uvarint length prefix, then
  UTF-8 text ending in `\n`, with the length counting the `\n`. The
  `Codec Msg` instance sits in the §3.2 instance list and proves the
  `LawfulCodec` round-trip. The 1 KiB cap applies before any payload
  allocation. The `ls` reply framing sits beside it: one message whose
  body holds `varint(len + 1) id \n` per supported id, ended by a final
  `\n` (the spike's `lsPayload`, kept).
- The core surface: `State`, `Event`, `Action`, and `step` (§3.3).
  `State` holds the role, the responder's ordered supported list, the
  input buffer, and the phase. `Event.bytes` carries raw bytes, and the
  core decodes them, so the malformed-versus-incomplete call stays in
  the core (§3.1). `Event.propose` posts the id the initiator dials.
  `Action.write` emits framed bytes, `Action.select` ends the
  negotiation with the chosen `ProtocolId` and the leftover, and
  `Action.error` reports `Negotiate.Error`. There is no tick: the
  upgrader owns the deadline (§5.4).
- `Reply` is the closed set of §3.4 with `na` and `ls`. Its wire form
  is the message text the codec carries, and no spec gives the replies
  a numeric code table, so it has no `toCode`/`ofCode?` pair, by the
  core pair's `Role` reasoning.
- `Negotiate.upgrade : Role → Connection → ByteArray → Option PeerId →
  List SecurityProtocol → List Muxer → ExceptT Core.Error IO
  (MuxSession × PeerId)` is the upgrader entry. The inputs: the
  `Connection`, which the host has already dialed or accepted (the host
  runs the upgrader inside its dial and accept paths, §4.9); the
  negotiation leftover; the expected `PeerId`, `none` on the listen
  path; and the two ordered lists (§3.1). The leftover is empty on a
  fresh dial, where no earlier stage can leave bytes. It is non-empty
  when an accept path peeked before it handed the connection over, or
  when the transport delivers bytes together with the connection. The
  output: the `MuxSession` and the verified remote `PeerId`; a pair or
  a small structure is a refinement this package fixes at
  implementation time. Errors surface as `Core.Error` (§3.5).

## The muxer-selection decision

The core pair left `SecureConn.remoteMuxers` out of the seam, and the
security pair decided the Noise payload keeps its extension bytes
opaque, with no advertisement in the outgoing payload. This pair
records the consequence: muxer selection negotiates on the wire through
multistream-select. The upgrader dials the `Muxer` ids in preference
order, and the responder answers `na` until a known id arrives. The
spike's extension path (`Upgrade.matchMuxers` over
`SecureConn.remoteMuxers`, with go's initiator-preference rule) stays
out: it would need a recorded `libp2p/core` refinement to carry the
bytes, and no root contract reads the extension. Interop is covered: a
go peer that selects from the extensions sees an empty advertisement
from us, and both sides fall back to the wire negotiation, the spike's
own fallback rule (the security pair records the same reasoning).
`MuxSession.openStream` carrying a `ProtocolId` (the mux pair,
decisions) is a stream-level label, and it plays no part in
connection-level selection.

## Owned contracts and how the package keeps them

1. **The 1 KiB cap applies before allocation** (§5.1, §4.9,
   PRINCIPLES 2.3). The check sits in the `Msg` decoder, ahead of the
   payload read. A length over `Negotiate.maxMsg` is a protocol error,
   and it tears the connection down (§5.2).
2. **The `na` retry.** The dialer moves to the next id of its ordered
   list on `na`. The responder answers `na` for an unknown id and stays
   in the negotiation. The spike's responder loop is the reference.
3. **`ls` support.** The responder answers the list when asked, with
   the framing above, and stays in the negotiation. The spike
   implemented the reply and its decode; the suites keep both.
4. **The lazy dialer.** The spike's order: propose the security id, run
   that handshake, compare the identity, then negotiate the muxer.
   Within each exchange, the dialer writes header and proposal
   back-to-back in one write and verifies both on first read
   (go-multistream `V1Lazy`; the spike's `selectInitiatorLazy`). The
   spike's upgrade path used the naive dialer at both exchanges.
   Go's upgrade traces and §4.9's "lazy dialer" bullet both name the
   lazy write, and the target moves it into the upgrade.
5. **Leftover hand-over between all three stages** (§4.7, §5.6). The
   negotiation leftover seeds the handshake; the `SecureConn` leftover
   seeds the muxer negotiation; the bytes that stage over-reads enter
   `Muxer.open` and become the first `Event` of the session loop (§4.7).
   Each stage owns one reader, and no two stages share a `BufReader`
   (§5.6).
6. **The 30 s deadline covers the whole unauthenticated upgrade**
   (§5.4). The upgrader wraps the three stages in one `withinDeadline`,
   with the constant from `Streams/Constants.lean`. Expiry closes the
   connection, and the parked reads end on their own (PRINCIPLES 3.1).
   An authenticated connection that sits idle never expires, because
   the deadline wraps the upgrade call alone.
7. **The upgrader imports `core` and no implementation** (§2, §3.1).
   The lists are parameters, and a new `SecurityProtocol` or `Muxer`
   value lands with no edit to the upgrader (PRINCIPLES 1.3).
8. **Errors map to `Core.Error` once, at the upgrade boundary** (§3.5).
   The core reports `Negotiate.Error`; `Upgrade.lean` lifts it with one
   `Except.mapError`, and a failed identity check reports
   `Core.Error.authentication`. The host matches on `Core.Error` alone.

## Decisions

- **A pure `step` for multistream-select** (§3.3, §9, delta 8). The
  spike kept the negotiation in IO functions over a shared `BufReader`.
  The target folds it into data in and data out, so a captured trace
  replays with no network and no clock (§6), and the `-N1` run holds by
  construction.
- **Wire-based muxer selection, against the spike's extension
  selection.** The section above records it.
- **The identity check sits between the handshake and the muxer stage,
  inside the upgrader** (§4.9). The pipeline order is
  security → identity check → muxer, so the check must gate the muxer
  stage. The upgrader compares `expected` against the
  `SecureConn.remotePeer` the handshake completed and fails with
  `Core.Error.authentication` before any muxer byte moves. The
  handshake still takes no expected id (the security pair, contract 4);
  the host supplies the expectation, the dial target on the dial path
  and `none` on the listen path. The spike's `upgradeOutbound` carried
  `expect : Option PeerId` and compared at the same place. This
  refines the security pair's wording, which says the host compares
  the completed `remotePeer`: the host supplies the expectation, and
  the upgrader performs the comparison, so the check gates the muxer
  stage as §4.9's pipeline orders it.
- **The upgrader takes a `Connection`, and the host dials.** The
  spike's `upgradeOutbound` called `transport.dial` itself. Root §4.9
  gives the dial and accept paths to the host, so the upgrader starts
  from the connection and stays free of the `Transport` seam.
- **The deadline home follows the streams pair** (contract 6 above).
  `Streams/Constants.lean` holds the 30 s value, and this package
  imports it. Two copies of a deadline drift like two copies of a cap
  (PRINCIPLES 1.5).

## What the package must not depend on

- Inside libp2p, `core` and `identity` only (§2: `identity → core → …
  → negotiate`). The identity check compares `PeerId` values, and
  `core` defines no re-export for the type, so this package imports
  `libp2p/identity` directly and records the import here, per the core
  pair's rule (the security pair records the same import). No import of
  `libp2p/security`, `libp2p/mux`, `libp2p/host`, or
  `libp2p/protocols`: the ordered lists carry the implementations.
- From the net group, `net/streams` for `Connection`, `BufReader`, and
  `readExactly` (§2: libp2p → net), recorded per the core pair's rule.
  The negotiation shell reads raw chunks through its own `BufReader`,
  one reader per stage (§4.7, §5.6). The frame decode and the cap live
  in the core, so the package has no `Framing` import.
- From the codec group, `codec/varint` only (§2). The multistream
  message is uvarint-length prefixed, so the varint appears, and the
  `Msg` codec imports the encoder and decoder of `codec/varint`.
- From `base`, `withinDeadline` from `base/conc`, and the byte model,
  `DecodeError`, and the `Codec`/`LawfulCodec` classes from
  `base/bytes`.
- No crypto. The security negotiation runs before the handshake. The
  muxer negotiation runs after it, over the `SecureConn`. No field
  names a key, a hash, or a cipher. No `codec/proto`: the multistream
  message is text, and no protobuf frame appears.
