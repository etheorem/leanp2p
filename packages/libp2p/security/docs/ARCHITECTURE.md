# leanp2p security: architecture

`libp2p/security` implements Noise XX
(`Noise_XX_25519_ChaChaPoly_SHA256`), the only security protocol the
eth2 networking spec names (§8). The handshake is a pure `step` (§3.3),
and a `SecurityProtocol` value wraps it (§4.9). A second value with
fixed keys is the test value (§3.1, §4.9). The noise suite is the
package's share of the libp2p row (§7 row 10). The TLS extension stays
deferred (§8): the spike's `Conn/TlsExt.lean` maps here (§10 row 13),
and no work is planned for it.

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Security.lean` | the root module; one import line per public submodule |
| `Libp2p/Security/Constants.lean` | the `/noise` protocol id, the protocol name string, the 65535-byte frame cap, and the 8 KiB payload cap; one home per fact (§3.8, PRINCIPLES 1.5) |
| `Libp2p/Security/Handshake.lean` | the pure core: `CipherState` and `SymmetricState` as data, `State`/`Event`/`Action`/`step`, and `Noise.Error`, the one error inductive of the package (§3.5) |
| `Libp2p/Security/Payload.lean` | the `NoiseHandshakePayload` protobuf, its `ProtoMessage` instance (§3.2), the signature input, and the 8 KiB gate |
| `Libp2p/Security/Transport.lean` | the framed AEAD reads and writes over the two cipher states of `split`, wrapped as the `SecureConn` surface |
| `Libp2p/Security/Noise.lean` | `Noise.securityProtocol`, the fixed-key test value, and the `Except.mapError` into `Core.Error` (§3.5) |

All declarations live in the `Libp2p.Security` namespace, and the root
module re-exports the public submodules. The values carry the names
§3.1 fixes: `Noise.securityProtocol`, and the fixed-key test value
beside it. The spike reference is `Conn/Noise.lean` (§10 row 13); the
target keeps its wire bytes, framing, and tests, and replaces the code
shape (§9, delta 8).

## Public surface

- The two `SecurityProtocol` values of §3.1 and §4.9:
  `Noise.securityProtocol`, and the fixed-key test value beside it.
  Both carry the `/noise` id and the §4.9 handshake signature,
  `handshake : Role → Connection → ByteArray → ExceptT Core.Error IO
  SecureConn`. The `ByteArray` argument is the negotiation leftover,
  and the `SecureConn` result holds the handshake's own leftover.
- The core surface: `State`, `Event`, `Action`, and `step` (§3.3),
  with `Noise.Error` as the package error inductive (§3.5).
- `NoiseHandshakePayload`, with its `ProtoMessage` instance (§3.2) and
  the 8 KiB gate.
- The framed AEAD reads and writes, exposed as the `SecureConn`
  surface of `core`: the secure read, write, and close, the peer ids,
  and the leftover.
- The constants of §3.8: the protocol id, the protocol name string,
  and the two caps.

The later sections carry the details; the surface names the entry
points.

## The core shape

The XX pattern runs as data-driven `step`s (§3.3). The initiator sends
`e`, the responder answers with `e, ee, s, es`, and the initiator
finishes with `s, se`. Each pattern token maps to one transition: `e`
mixes a public key into the running hash, `ee`, `es`, and `se` mix a
Diffie-Hellman result into the chaining key, `s` carries the encrypted
static key, and each message ends with its encrypted payload. `split`
derives the two transport cipher states at the end. The symmetric state
opens with `h = ck =` the protocol name (zero-padded when shorter than
32 bytes, hashed only when longer), and the cipher nonce is 4 zero
bytes followed by the 8-byte little-endian counter.

The state is plain data: the symmetric state, the role, the local
static key, the remote static and ephemeral keys as the handshake
learns them, and the input buffer. The buffer opens with the
negotiation leftover (§4.9), so the handshake consumes handed-on bytes
before it reads the connection (§4.7, §5.6).

The events carry the world in: `bytes` delivers one framed message,
which the shell reads through the 2-byte length prefix with
`readExactly`. `local` posts the local static Noise key and the
marshaled handshake payload; the shell builds the payload once, through
the facade and the sign dispatch of `libp2p/identity`, and a secp256k1
identity draws a random signature nonce (§3.6), so the built payload is
an input. `entropy` posts 32 bytes from the `Rng` seam of the facade
(§3.6), and the core derives the X25519 keypair from them at the `e`
token. The event set has no tick: the core has no use for time, and
the upgrader owns the deadline (§5.4, contract 7 below).

The actions carry the world out: `write` emits framed bytes,
`complete` ends the handshake with the two cipher states of `split`,
the local and remote `PeerId`s, and the leftover bytes the handshake
over-read, and `error` reports a `Noise.Error`. The loop tears the
connection down on `error` (§3.5).

The transport keeps the same shape at the small scale it has: the two
cipher states are data, and one frame in or out is one pure transition
over them. The framed IO path types as `ExceptT Noise.Error IO` (§3.5),
and keys and nonces cross the facade as the proof-carrying newtypes
`Key32` and `Nonce12` (§3.7). Where the proofs sit: the crypto arrives
through the `Crypto` facade, which names the backend for every
primitive it binds, the digests included (the crypto pairs; §4.6), and
§3.3 allows a core to call
pure externs. The core is deterministic in its events, and the
transcript tests replay it with no task, no network, and no clock (§6).
The 2-byte framing codec proves its round-trip directly over the byte
model, as the spike proved `be16_roundtrip`; the generic-harness route
would need a wrapper newtype for the length, because §3.2 puts no
instance on a core type.

## Owned contracts and how the package keeps them

1. **A failed AEAD open is a protocol error, distinct from EOF, and it
   tears the connection down** (§3.5, §4.9). The backend gives the open
   failure its own `CryptoError` arm (the backend pair, public
   surface), and the seam value maps it to `Core.Error.protocol` with
   `Except.mapError`. The read path tears the connection down first and
   reports `none` only after, so a downstream layer treats EOF as an
   orderly event (PRINCIPLES 2.4).
2. **The 8 KiB payload cap applies before the pre-authentication
   decode** (§4.9, §5.1). The gate sits in `Payload.lean`, ahead of the
   protobuf decode. The spike's reason stands: the list-based decoder
   cost quadratic time, and a real payload stays under 2 KiB even with
   an RSA-8192 identity (PRINCIPLES 2.3).
3. **The 64 KiB frame cap** (§5.1). The 2-byte length prefix bounds a
   message at 65535 bytes. The write path chunks plaintext at 65535 −
   16, because the Poly1305 tag counts against the cap. Both numbers
   live in `Constants.lean`; the spike's write path re-derived its
   chunk size and drifted from the cap until the review caught it
   (PRINCIPLES 1.5).
4. **The static-key check** (§4.9). The payload's signature covers
   `noise-libp2p-static-key:` plus the static Noise public key, and it
   must verify against the identity key in the same payload. A failure
   maps to `Core.Error.authentication` at the seam. The identity key
   derives the `PeerId` the completion action carries. The comparison
   against the expected id gates the muxer stage of the upgrade (§4.9:
   the pipeline runs security → identity check → muxer); the handshake
   takes no expected id, the host supplies the expectation, and the
   upgrader compares the completed `remotePeer` against it (the
   negotiate pair's refinement). The spike split it the same way.
5. **The leftover hand-over runs in both directions** (§4.7, §4.9,
   §5.6). In: the `ByteArray` argument of the handshake seeds the input
   buffer, ahead of any connection read. Out: the `SecureConn` carries
   the bytes the handshake over-read, and they seed the transport
   reader. With §5.6 this keeps one reader per stream. The spike shared
   one `BufReader` across negotiation, handshake, and transport; the
   target passes bytes as data (§4.7).
6. **A failed seal tears the connection down** (§4.9). The write loop
   stops, the close runs, and both ends observe the failure.
7. **The deadline covers the handshake** (§5.4). The 30 s budget is the
   unauthenticated phase's, and its one home is `Streams/Constants.lean`
   (the streams pair). The upgrader (W5.5) wires it with
   `withinDeadline` around the handshake shell. Expiry closes the
   connection, and the parked read ends on its own (PRINCIPLES 3.1).
8. **Verify before trust** (§5.2, PRINCIPLES 2.4). No unauthenticated
   byte allocates past its cap: the framed read takes the 65535 cap
   before any payload allocation, and the payload decode runs only
   under the 8 KiB gate.

## The handshake extensions

The payload protobuf carries an extension field beside the identity key
and the signature. go-libp2p advertises its muxer list there and may
select the muxer from it. The spike parsed the field, carried the list
in `SecureConn.remoteMuxers`, and applied go's rule: the initiator
orders by its own preference, the responder follows the initiator, and
otherwise both fall back to multistream-select. The core pair left the
field out of `SecureConn` and assigned the handshake extensions to this
pair (the core pair, module map).

The decision: the extension bytes stay opaque. `Payload.lean` decodes
the identity key and the signature, and keeps the extension field as
bytes without reading names out of them. The reason: the `Muxer` seam
of §4.9 negotiates on the wire through multistream-select, no root
contract reads the extension, and a parsed list with no consumer is
dead code. The bytes stay in the decoded payload. Extension-based
selection can reach them only through a field on the core seam: the
upgrader imports `core` and no implementation (§2, §9, delta 10), so
the refinement lands in `libp2p/core`, and W5.5 records whether muxer
selection reads them or negotiates on the wire. The outgoing payload
carries the identity key and the signature and no muxer advertisement,
and a peer without the extension falls back to the wire negotiation,
the spike's own recorded rule.

## Decisions

- **A pure core plus a transport value, against the spike's mutable
  session** (§3.3, §9, delta 8). The spike's `HandshakeState` was
  already data, but its shell held the transport ciphers in `IO.Ref`s
  and returned `Option` from every step (§9, delta 9), with an `efix`
  field bolted on for replay. The target folds the machine into
  `step`, types the errors, and feeds replay through the events. Every
  primitive the core touches is pure through the facade (§3.6), so the
  same events give the same actions, and the transcript suites rest on
  that determinism.
- **Randomness and the payload are events** (§3.3). The spike drew the
  ephemeral mid-handshake from the backend. The shell here draws the
  entropy from the `Rng` seam and posts it, so a test replays the
  handshake with fixed events and no seam behind the core.
- **The fixed-key test value** (§3.1, §4.9). Fixed static keys and
  fixed entropy events drive both roles, and the test identity is
  Ed25519, whose signature is deterministic (§3.6), so the suites
  above the transport run the real Noise path with no randomness.
- **No rekey.** The spike had none, and the vendored noise-libp2p spec
  (r5) defines none. Each transport cipher state runs its counter
  toward 2^64 − 1 nonces and never reaches them in a session's life.

## What the package must not depend on

- Inside libp2p, `core` and `identity` only (§2: identity → core →
  security). The `SecureConn` inputs and the error target come from
  `core`; the payload's key checks and the `PeerId` derivation come
  from `identity`. No import of `libp2p/negotiate`, `libp2p/mux`,
  `libp2p/host`, or `libp2p/protocols`.
- Crypto reaches the package through the `Crypto` facade only (§3.6):
  SHA-256, HKDF, X25519, and ChaCha20-Poly1305. No `crypto/backend` and
  no `crypto/pure` import. The signature checks go through the sign
  and verify dispatch of `libp2p/identity`.
- From `net/streams`, `Connection` and `readExactly`. The handshake
  signature of §4.9 names `Connection`, and core defines no re-export
  for it, so this package imports `net/streams` directly and records
  the import here, per the core pair's rule. The direction is the
  group-legal one (§2: libp2p → net).
- No knowledge of multistream-select, yamux, or mplex bytes. The
  negotiation hands this package bytes through the leftover argument,
  and the handshake consumes them without knowing what produced them.
