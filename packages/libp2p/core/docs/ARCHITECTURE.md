# leanp2p libp2p core: architecture

Core defines the shared libp2p types and interfaces of root
ARCHITECTURE §3.1 and §4.9. It contains no protocol implementation.
Security, mux, negotiate, and host depend on these interfaces;
`cli/` supplies the implementation values as configuration.

## Modules

All declarations use `Libp2p.Core`. `Libp2p.Core` re-exports the public
modules. Operation contracts are documented beside their declarations.

| Module under `Libp2p/` | Surface |
|---|---|
| `Core.lean` | Public imports |
| `Core/ProtocolId.lean` | `ProtocolId` and its instances |
| `Core/Error.lean` | `Core.Error`, rendering, and error mapping |
| `Core/Security.lean` | `Role`, `SecureConn`, `SecurityProtocol` |
| `Core/Mux.lean` | `MuxSession`, `Muxer` |
| `Core/Handler.lean` | `StreamHandler` |
| `Core/Policy.lean` | `Decision`, `ConnectionGater`, `ResourceScope`, `ConnectionScope`, `ResourceManager`, `AddressRanker` |
| `Core/Mock/` | Temporary dependency interfaces, listed below |

## Public surface

| Type | Purpose |
|---|---|
| `ProtocolId` | Exact protocol-name equality, hashing, ordering, and text rendering |
| `Core.Error` | `protocol`, `authentication`, `timeout`, and `closed`, each with rendered detail |
| `Role` | Local `initiator` or `responder` direction |
| `SecurityProtocol`, `SecureConn` | Handshake, authenticated identities, secure connection, and leftovers |
| `Muxer`, `MuxSession` | Session creation, stream creation and acceptance, shutdown, and completion |
| `StreamHandler` | Callback registered by protocol id |
| `ConnectionGater` | Admission before dial, after accept, and after authentication |
| `ResourceManager`, `ConnectionScope`, `ResourceScope` | Connection and stream grants with memory accounting |
| `AddressRanker` | Address ordering with a permutation proof |

### Test values

Core's doubles live in `Tests/Libp2pCore.lean`. The implementation
packages own the production and test values required by §3.1: security
provides fixed-key handshakes, mux provides a test muxer, and host
provides policy values. Streams owns the sim transport.

## Owned contracts

- Core holds types and interfaces only (§4.9). It defines no codecs,
  protocol state machines, or protocol-id constants.
- Negotiated interfaces carry `id : ProtocolId` (§3.1, §3.4).
  Protocol constants belong to their implementation packages.
- Implementations map protocol failures to `Core.Error` at the seam.
  System faults remain thrown `IO.Error`s (§3.5).
- Operations that can park use `Conc.Async` (§4.1). Session owners
  close and then join; completion waits for all owned tasks.
- Each stage consumes handed-over bytes before reading its connection.
  No two stages share a reader (§4.7, §5.6).
- Interface fields expose no mutable cells. Session state belongs to
  the implementation's loop (§3.1, §3.3).
- Implementation lists come from configuration (§3.1).

## Decisions

- **Protocol ids:** follow §3.4's string wrapper. The multistream
  codec owns wire validation and size limits. This resolves the
  reference to `ProtocolId` among §3.7's proof-carrying types.
- **Roles:** no spec assigns roles numeric wire codes, so `Role`
  derives the §3.4 classes without a `toCode`/`ofCode?` table.
- **Errors:** each variant stores rendered implementation detail.
  Core can preserve diagnostics without importing concrete errors.
- **Secure connections:** `SecureConn` holds a `Connection`; the
  upgrader passes `sc.conn` to the muxer explicitly. Ciphertext left
  after a handshake stays with the security transport reader;
  `SecureConn.leftover` is at the plaintext level of `conn`.
- **Muxers:** one `open` operation takes the role for stream-id
  assignment. `openStream` takes a `ProtocolId` label, as specified
  by the mux package. Mplex transmits the label and yamux ignores it;
  stream protocol negotiation still follows.
- **Resource scopes:** stream grants come from their connection scope.
  `setPeer` associates the authenticated peer, allowing both peer and
  connection limits to account for the same resources.
- **Address ranking:** the permutation proof preserves addresses and
  their multiplicities. Repeated input addresses remain repeated.

The spike references are `Conn/Security.lean` and
`Conn/Upgrade.lean` (`MuxHandle`, `MuxChoice`). Core replaces their
string ids and `Option` failures with the types above. Session
completion replaces `MuxHandle.isDead` and its exposed task set.
`SecureConn.remoteMuxers` is omitted; the security and negotiate
packages document wire-based muxer selection.

## The mocks

W4.1 and W5.1 are pending. `RULES.md`, "Working ahead of the tree",
permits mocks of their frozen interfaces. The mocks import no real
dependency implementation and introduce no dependency theorem axioms.

| Mock under `Libp2p.Core.Mock` | Surface | Replacement |
|---|---|---|
| `Streams` | Opaque `Connection`, `Stream`, and `Connection.close` | `Streams` after W4.1 |
| `Identity` | Opaque `PeerId` | `Libp2p.Identity` after W5.1 |
| `Multiformats` | Opaque `Multiaddr` | Address type available through streams, backed by W2.3 |

Opening `Libp2p.Core.Mock` makes qualified names such as
`Streams.Connection` resolve to the temporary types. No mock exposes
constructors. `Connection.close` has a no-op body for compilation;
the mocks exercise no transport behavior.

Integration steps:

1. Replace the mock imports in core with `Streams` and
   `Libp2p.Identity`, as needed by each module. Use the address type
   exposed by the integrated streams dependency.
2. Remove `open Libp2p.Core.Mock` from core and the tests, then delete
   `Libp2p/Core/Mock/`.
3. Assemble the test values over the real sim transport and peer ids.
4. Run the build, both test modes, and import lint listed in `PLAN.md`.
   Verify name resolution and signatures against the real dependencies.

Mocks must be removed before merge, after both blocking dependencies
have merged. Changes to frozen interfaces follow `RULES.md`'s approval
process.

## What the package must not depend on

Core depends on identity for `PeerId`, streams for connections,
streams, and addresses, and conc for asynchronous effects (§4.9).
It imports no codec directly and names no crypto primitive. Imports
of security, mux, negotiate, host, and protocols are forbidden; the
import lint checks package direction (§2).
Consumers record additional direct dependencies in their own package
architecture.
