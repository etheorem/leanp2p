# leanp2p libp2p core: architecture

`libp2p/core` holds the libp2p-wide types, with no protocol logic
(§4.9). It defines `ProtocolId`, `Core.Error`, and the seam structures
every implementation fills: `SecurityProtocol` with `SecureConn`,
`Muxer` with `MuxSession`, `StreamHandler`, and the policy hooks
(§3.1, §4.9). It is the import seam of the libp2p group.
Implementations import it. The upgrader of `libp2p/negotiate` imports
it and no implementation (§2). `cli/` assembles the ordered lists
through it (§3.1). The spike defined each seam next to its first
implementation, so its upgrader imported Noise and yamux; this package
removes that coupling (§9, delta 10).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Core.lean` | the root module; one import line per public submodule |
| `Libp2p/Core/ProtocolId.lean` | the wrapped-string protocol id, with its derived classes (§3.4) |
| `Libp2p/Core/Error.lean` | `Core.Error`, the coarse error every seam returns (§3.5, §4.9) |
| `Libp2p/Core/Security.lean` | `Role`, `SecureConn`, and the `SecurityProtocol` seam |
| `Libp2p/Core/Mux.lean` | the `Muxer` seam and `MuxSession` |
| `Libp2p/Core/Handler.lean` | `StreamHandler`, the callback a served stream reaches |
| `Libp2p/Core/Policy.lean` | the connection gater, the resource manager, and the address ranker |

All declarations live in the `Libp2p.Core` namespace, and the root
module re-exports the public submodules, so an implementation or the
upgrader imports one name.

The package has no constants module. `ProtocolId` constants live with
their protocols, one module per package (`Mux.yamuxId`,
`Identify.protocolId`, §3.4), so core owns the type and holds no
constants of it. The caps and deadlines a reader might expect here
belong to the packages that enforce them (§5.1, §5.4). §3.8's
one-constants-module rule has nothing to bind in this package.

The spike reference is `Conn/Security.lean` for the security seam
shape and `Conn/Upgrade.lean` for `MuxHandle` and `MuxChoice` (§10
row 12). The spike shapes change here: the `name : String` fields
become `id : ProtocolId` (§3.4), the `BufReader` arguments become a
`Connection` plus a leftover `ByteArray` (§4.7, §4.9), and the
`Option` results become `ExceptT Core.Error IO` (§3.5). The spike's
handshake implementation, `Conn/Noise.lean`, maps to
`libp2p/security` (§10 row 13). Two spike fields drop out of the
surface. The spike's `SecureConn.remoteMuxers` carried the muxer list
the Noise extensions advertise, and this surface leaves it out: the
security pair (W5.3) owns the handshake extensions, and the negotiate
pair (W5.5) records whether muxer selection reads them or negotiates
on the wire. The spike's `MuxHandle.isDead` flag is subsumed by the
session completion of `MuxSession`.

## Public surface

The shapes are §4.9's, refined where this section says so.

- `ProtocolId` is the open set of §3.4: `structure ProtocolId where
  toString : String`, with derived `DecidableEq` and `Hashable`.
  Peers define ids, so the set stays open. Code compares `ProtocolId`
  values only (§3.1).
- `Core.Error` is the coarse inductive of §4.9, with the four arms
  `protocol`, `authentication`, `timeout`, and `closed`. Each arm
  carries the error of the implementation, in its rendered form. The
  upgrader and the host act on this one type (§3.5), and the log
  keeps the detail through the rendered payload.
- `Role` is the closed set with `initiator` and `responder` (§4.9).
  It derives the standard classes (§3.4). No spec gives roles a wire
  code, so it has no `toCode`/`ofCode?` pair; the total maps arrive
  only if a code table appears.
- `SecurityProtocol` carries `id : ProtocolId` and the handshake of
  §4.9: `handshake : Role → Connection → ByteArray → ExceptT
  Core.Error IO SecureConn`. The `ByteArray` argument holds what the
  negotiation over-read, and the handshake consumes it before it
  reads the connection (§4.7).
- `SecureConn` is the post-handshake connection: the secure read,
  write, and close surface over the underlying `Connection`, the
  `localPeer` and `remotePeer` ids of §4.9's identity check, and the
  leftover `ByteArray` the handshake over-read. The leftover seeds
  the reader of the next stage (§4.7, §5.6). Lifecycle is part of the
  seam (§3.1): `SecureConn` exposes `close`, over the close of the
  underlying `Connection`, plus the completion the owner joins. The
  spike's `SecureConn extends Connection` is the reference form
  (§10 row 12); whether the type extends or holds the `Connection` is
  a refinement this package fixes at implementation time.
- `Muxer` carries `id : ProtocolId` and the field that opens a
  session. The spike split the directions into `MuxChoice.client` and
  `MuxChoice.server`; this package follows the `SecurityProtocol`
  shape and carries one field, `open : Role → Connection → ByteArray
  → ExceptT Core.Error IO MuxSession`. The direction matters to every
  muxer: yamux assigns stream ids by the parity of the direction
  (§4.8).
- `MuxSession` is the uniform session view: `openStream`, which
  returns a fresh `Stream` through `ExceptT Core.Error IO`;
  `accept : IO (Option Stream)`, which returns `none` when the
  session closes, so a parked accept wakes and ends, as
  `Listener.accept` in `net/streams` does; `close : IO Unit`; and the
  completion of the session loop, which the owner joins (§3.1, §4.1).
  Whether `openStream` carries the protocol hint mplex needs in its
  NewStream frame is a refinement `libp2p/mux` records.
- `StreamHandler` carries `id : ProtocolId` and `handle : Stream →
  ExceptT Core.Error IO Unit`. The host keys its registry by the id
  (§3.10), and a served stream reaches the callback. Whether a
  handler failure closes the connection is the host's call, so the
  exact return form is the seam's to refine with the host pair.
- The policy hooks are three structures in `Policy.lean`. The gater
  answers allow or deny for an outbound dial and for an inbound
  connection. The resource manager answers whether a new connection
  or stream fits the limits, and §9 (delta 4) names the limits:
  stream count, buffered bytes, and a memory ceiling, per peer and
  per connection. The address ranker orders a peer's addresses for
  dialing. §4.9 fixes the three hooks and no signatures, so the
  decision inputs beyond these are the seam's to refine as the host
  lands (W5.6).

**Test values.** §3.1 gives every seam two values from the start, the
production value and a test value, and every suite above the
transport runs on the test values (PRINCIPLES 1.4). The test values
live with their implementations: the fixed-key security protocol is a
second `SecurityProtocol` value in `libp2p/security` (§4.9), and a
`Muxer` test value with fixed ids belongs to `libp2p/mux`. The sim
transport is the `Transport` test value and lives in `net/streams`.
A `StreamHandler` double exists for the compile milestone of this
package's plan. The policy doubles, a permissive gater and a denying
gater among them, belong to the host pair (W5.6), whose consumers
they are. Core itself provides types only. Its contribution is that
the shapes admit the test values, which the compile milestones of
this package's plan check.

## Owned contracts and how the package keeps them

1. **Types only, with no protocol logic** (§4.9). The package holds
   no `step`, no codec, and no match on wire bytes. Review enforces
   this; the package is small enough to read in one sitting.
2. **Every negotiated seam carries `id : ProtocolId`, and code
   compares `ProtocolId` values only** (§3.1, §3.4). `SecurityProtocol`,
   `Muxer`, and `StreamHandler` each carry the field. A string
   literal in this package is a review failure; the literals live in
   the protocol packages' id modules.
3. **A seam value holds no protocol decisions** (§3.1). Its fields
   call a core and move bytes. A seam field that needs a `match` on
   wire data puts the match into the core of the implementation
   package.
4. **Lifecycle is part of the seam** (§3.1, §4.1). `SecureConn` and
   `MuxSession` expose `close : IO Unit` and a completion the owner
   joins. The owner closes, then joins (PRINCIPLES 3.2). No seam
   value spawns an unowned task.
5. **A seam exposes no `IO.Ref`** (§3.1). State belongs to the loop
   task behind the seam (§3.3) or to a host registry (§3.8). The
   structure fields here are data and functions, never a bare cell.
6. **The error mapping happens once, at the seam value, with
   `Except.mapError`** (§3.5). The implementation maps its own error
   into `Core.Error` at its seam value; the upgrader and the host
   match on `Core.Error` alone, and `libp2p/host` wraps it in
   `Host.Error` (§3.5, §4.9).
7. **The ordered lists are configuration** (§3.1). No code below
   `cli/` hard-codes which transport, security protocol, or muxer
   exists. The structures here carry no default lists and no single
   implementation's name.

## Decisions

- **The seam types live in `core`, beside no implementation** (§9,
  delta 10). The spike's upgrader imported
  Noise and yamux to name their seam types, so the dispatcher knew
  two concrete implementations. Here the upgrader imports `core`
  only, and a new security protocol or muxer lands as a new value
  with no edit to the upgrader (PRINCIPLES 1.3). §10 row 12 records
  the move.
- **`Core.Error` is coarse, and each arm carries the rendered inner
  error** (§3.5, §4.9). The upgrader and the host act on one type,
  and the log keeps the detail. A fine-grained union of every
  implementation's error type would pull each implementation's types
  into core, and the package would import them again.
- **`ProtocolId` stays an open wrapped string** (§3.4). Peers define
  protocol ids, so no closed set can hold them, and the derived
  `DecidableEq` and `Hashable` serve the registry lookups of §3.10.
- **`Role` carries no codes.** §3.4 demands the total maps for a
  closed set with a spec code table. No libp2p spec puts a role on
  the wire; the direction travels as the muxer's id parity and the
  handshake's message order. Adding maps without a table would invent
  codes, so the package derives the classes and stops there.
- **The muxer seam folds the spike's client and server entries into
  one field with a `Role`.** One field per seam keeps the two seams
  parallel, and the parity rules stay inside the implementation
  packages, where the spike kept them (§10 row 12).

## What the package must not depend on

- Inside libp2p, `identity` only, for `PeerId` (§2, §4.9). No import
  of `libp2p/security`, `libp2p/mux`, `libp2p/negotiate`,
  `libp2p/host`, or `libp2p/protocols`. The import lint of §2 fails
  the reverse direction, and review fails the forward one.
- Core names no crypto type. `SecurityProtocol.handshake` moves key
  material as a `ByteArray`, and no field mentions a key, a hash, or
  a cipher by name (§4.9). The key-material types belong to
  `libp2p/identity`, and core reaches them only through `PeerId`.
- From below, `net/streams` for `Connection` and `Stream` (§4.9).
  §4.9 says core depends on `identity` and `net/streams` and on
  nothing else, so the package writes no direct import of a codec or
  a base module; `base/conc` and `base/bytes` arrive through
  `net/streams`. Core names no base or codec name of its own. If a
  refinement needs one, the direct import is recorded here as part of
  that refinement.
- No protocol knowledge of any kind: no Noise message, no yamux
  header, no multistream reply. The package is the seam, and the
  implementations own the bytes.
