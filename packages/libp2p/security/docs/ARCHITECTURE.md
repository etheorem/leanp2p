# leanp2p security: architecture

`libp2p/security` implements the two security protocols of the eth2
networking spec. Noise XX (`Noise_XX_25519_ChaChaPoly_SHA256`) secures
the TCP transport. The libp2p TLS handshake (`vendor/specs/tls/tls.md`)
secures the QUIC transport
(`vendor/consensus-specs/specs/phase0/p2p-interface.md`, lines 179 to
180: "The QUIC transport is secured using TLS 1.3, configured
according to the libp2p TLS specification"). This package runs it over
TCP as `/tls/1.0.0`, and the QUIC transport (`libp2p/quic`, root PLAN
W4.4) reuses its certificate and its checks. The Noise handshake is a pure `step` (§3.3), and a `SecurityProtocol`
value wraps it (§4.9). A second value with fixed keys is the test
value (§3.1, §4.9). The TLS
1.3 engine is `net/tls`, and this package holds the libp2p part of TLS:
the certificate, its checks, and the seam value. The spike's
`Conn/TlsExt.lean` maps to `Libp2p/Security/Tls/` (§10 row 13). The
noise and TLS suites are the package's share of the libp2p row (§7
row 10).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Security.lean` | the root module; one import line per public submodule |
| `Libp2p/Security/Constants.lean` | the `/noise` protocol id, the protocol name string, the 65535-byte frame cap, and the 8 KiB payload cap; one home per fact (§3.8, PRINCIPLES 1.5) |
| `Libp2p/Security/Handshake.lean` | the pure core: `CipherState` and `SymmetricState` as data, `State`/`Event`/`Action`/`step`, and `Noise.Error`, the one error inductive of the package (§3.5) |
| `Libp2p/Security/Payload.lean` | the `NoiseHandshakePayload` protobuf, its `ProtoMessage` instance (§3.2), the signature input, and the 8 KiB gate |
| `Libp2p/Security/Transport.lean` | the framed AEAD reads and writes over the two cipher states of `split`, wrapped as the `SecureConn` surface |
| `Libp2p/Security/Noise.lean` | `Noise.securityProtocol`, the fixed-key test value, and the `Except.mapError` into `Core.Error` (§3.5) |
| `Libp2p/Security/Tls/Constants.lean` | the `/tls/1.0.0` id, the extension OID, the signature prefix, the ALPN name, the certificate times, and the DER length cap; one home per fact (§3.8) |
| `Libp2p/Security/Tls/SignedKey.lean` | the `SignedKey` DER codec over the byte model, with the round trip as a theorem |
| `Libp2p/Security/Tls/Certificate.lean` | `Tls.verify`, the libp2p checks of a peer certificate, with `Tls.CertError`; `Tls.Identity`, our issued certificate, with `Tls.IssueError` |
| `Libp2p/Security/Tls/Protocol.lean` | `Tls.Config`, `Tls.certificateCheck`, the check the engine runs, `Tls.securityProtocol`, the seam value over the engine of `net/tls`, and the fixed-key test value `Tls.fixedKeyProtocol` |

All declarations live in the `Libp2p.Security` namespace, and the root
module re-exports the public submodules. §3.1 names the production
value `Noise.securityProtocol`, and the fixed-key test value beside it
is `Noise.fixedKeyProtocol`. TLS has the same pair,
`Tls.securityProtocol` and `Tls.fixedKeyProtocol`. The spike reference
is `Conn/Noise.lean` (§10 row 13); the target keeps its wire bytes,
framing, and tests, and replaces the code shape (§9, delta 8).

## Public surface

- The two `SecurityProtocol` values of §3.1 and §4.9:
  `Noise.securityProtocol cfg`, and the fixed-key test value
  `Noise.fixedKeyProtocol cfg seed` beside it. A `Noise.Config` holds
  the identity key and the Noise static key; `Config.generate` draws
  the static key from `Rng.system`. Both values carry the `/noise` id
  and the §4.9 handshake signature,
  `handshake : Role → Connection → ByteArray → ExceptT Core.Error Async
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
- The TLS value `Tls.securityProtocol cfg`, with the `/tls/1.0.0` id
  and the same §4.9 handshake signature. A `Tls.Config` holds the
  peer id of the host key, our certificate, the engine context, the
  wall clock of the validity check, and the monotonic clock of the
  `close_notify` bound. `Config.generate` draws the certificate key;
  `Config.ofCertKey` takes one. The test value is
  `Tls.fixedKeyProtocol key certKey now`, over `Config.fixed`: fixed
  keys, and a wall clock fixed at `now`.
- `Tls.verify der now`: the libp2p checks of a peer certificate, with
  one `Tls.CertError` arm per check. The QUIC transport calls it too.
  `Tls.certificateCheck now` is the same check in the form the engine
  takes, `ByteArray → Option String`. `Tls.identity der` runs every
  check but the validity window: the read of the peer after a
  handshake whose check already ran `verify`. `Tls.identity_of_verify`
  states that the two agree.
  `Tls.Identity.issue` and `Identity.generate`: our certificate, with
  `Tls.IssueError` for a failed issue. `Tls.SignedKey`: the extension
  value.

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

The core is the Noise layer, over opaque payloads. The noise-libp2p
spec carries the libp2p payload inside messages 2 and 3, and checks it
on receipt: "Upon receiving the handshake payload, peers MUST decode
the public key from the `identity_key` field … The key MUST then be
used to validate the `identity_sig` field" (the spec, "The libp2p
Handshake Payload"). go keeps flynn's `HandshakeState` below that check
(`vendor/go-libp2p/p2p/security/noise/handshake.go`, `runHandshake` and
`handleRemoteHandshakePayload`), and js keeps `XXHandshakeState` below
`decodeHandshakePayload`
(`vendor/js-libp2p/packages/connection-encrypter-noise/src/performHandshake.ts`). The flynn vectors
carry raw payloads and a prologue, so they test the core alone.

The state is plain data: the symmetric state, the phase of the role
with the remote static and ephemeral keys as the handshake learns
them, and the local static key. The static key and the prologue enter
when the state is built, as flynn's `NewHandshakeState` takes them
(`Config.Prologue`, `Config.StaticKeypair`; `vendor/flynn-noise`,
`state.go`). js passes `s` to the `XXHandshakeState` constructor, and
nim sets `hs.s` before the first message
(`vendor/nim-libp2p/libp2p/protocols/secure/noise.nim`, lines 379 and
420).

The events carry the world in: `bytes` delivers one framed message,
which the shell reads through the 2-byte length prefix with
`Streams.Framing.read`; flynn's `ReadMessage` takes one whole message
the same way. The negotiation leftover seeds that framed reader (§4.9), so the
handshake consumes handed-on bytes before it reads the connection
(§4.7, §5.6). `local` posts the marshaled payload of our next
handshake message, as flynn's `WriteMessage` takes one payload per
message; the shell builds the libp2p payload once, through the facade
and the sign dispatch of `libp2p/identity`, and a secp256k1 identity
draws a random signature nonce (§3.6), so the built payload is an
input. `entropy` posts 32 bytes from the `Rng` seam of the facade
(§3.6), and the core derives the X25519 keypair from them at the `e`
token. The event set has no tick: the core has no use for time, and
the upgrader owns the deadline (§5.4, contract 7 below).

The actions carry the world out: `write` emits framed bytes,
`payload` hands out the peer's decrypted payload of one handshake
message, and `complete` ends the handshake with the two cipher states
of `split` and the remote static key. `step` returns `Except
Noise.Error` (root §3.3), and the loop tears the connection down on an
error (§3.5).

The shell performs the actions in order, and it checks each `payload`
action with `Noise.verify` before the next one. The check answers the
identity key and the `PeerId` it derives (contract 4), and the seam
value puts the local and remote `PeerId`s into the `SecureConn`. On
the initiator, the payload of message 2 comes out before the write of
message 3, so a bad payload ends the connection before message 3
reaches the wire, as go and js order it
(`vendor/go-libp2p/p2p/security/noise/handshake.go`, lines 78 to 102;
`vendor/js-libp2p/packages/connection-encrypter-noise/src/performHandshake.ts`,
lines 32 to 42). The bytes that the framed
reader holds past the last message are transport ciphertext, and they
seed the transport reader (contract 5); rust-libp2p keeps them the
same way, in the read buffer that `map_into_transport` hands on
(`vendor/rust-libp2p/transports/noise/src/io/handshake.rs`, line 157).

The transport keeps the same shape at the small scale it has: the two
cipher states are data, and one frame in or out is one pure transition
over them. The handshake shell types as `ExceptT Noise.Error Async`
(§3.5; `Async` is the form `IO` takes for a step that parks, the core
pair). The transport reports a `Noise.Error` through the completion of
its tasks, which the seam value maps into the `SecureConn.join`. Keys and nonces cross the facade as the proof-carrying newtypes
`Key32` and `Nonce12` (§3.7). Where the proofs sit: the crypto arrives
through the `Crypto` facade, which names the backend for every
primitive it binds, the digests included (the crypto pairs; §4.6), and
§3.3 allows a core to call
pure externs. The core is deterministic in its events, and the
transcript tests replay it with no task, no network, and no clock (§6).
The 2-byte framing codec is the `u16be` prefix of `Streams.Framing`,
the one home of the Noise frame (the streams pair, "Two prefix shapes
exist, `uvarint` and `u16be` (the Noise frame)"). Its `Frame` newtype
carries the `LawfulCodec` proof of the round trip over the byte model,
so this package imports it and proves it a second time nowhere
(PRINCIPLES 1.5).

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

   > **Note.** The 8 KiB value comes from root §5.1. The spec sets no
   > payload limit below the 65535-byte message, and the references
   > decode the payload with no limit of their own: go-libp2p
   > (`vendor/go-libp2p/p2p/security/noise/handshake.go`, line 252),
   > rust-libp2p (`vendor/rust-libp2p/transports/noise/src/io/framed.rs`,
   > lines 36 and 134), js-libp2p
   > (`vendor/js-libp2p/packages/connection-encrypter-noise/src/utils.ts`,
   > line 37), and nim-libp2p
   > (`vendor/nim-libp2p/libp2p/protocols/secure/noise.nim`, lines 566
   > and 567). A payload between 8 KiB and 64 KiB passes there and fails
   > here.
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
   derives the `PeerId` that `Noise.verify` answers, and the seam value
   puts it into `SecureConn.remotePeer` (the core shape). The comparison
   against the expected id gates the muxer stage of the upgrade (§4.9:
   the pipeline runs security → identity check → muxer); the handshake
   takes no expected id, the host supplies the expectation, and the
   upgrader compares the completed `remotePeer` against it (the
   negotiate pair's refinement). The spike split it the same way.
5. **The leftover hand-over runs in both directions** (§4.7, §4.9,
   §5.6). In: the `ByteArray` argument of the handshake seeds its
   framed reader, ahead of any connection read. Out: the `SecureConn` carries
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
9. **Every MUST of the TLS spec's "Peer Authentication" has a check.**
   The engine checks the version, the client certificate, the chain of
   one, and the ALPN name (`net/tls`, owned contract 1). `Tls.verify`
   checks the extension, a repeated extension, the unknown critical
   extensions, the self-signature, the validity window, and the host
   key's signature. The backend names the extension rule that a
   refused certificate broke (`Crypto.CertificateRejection`), so each
   check has its own `CertError` arm.
   The upgrader compares the derived peer id with the expected one, as
   for Noise (contract 4).
10. **No TLS byte reaches a caller before the certificate check.** The
    engine runs `Tls.verify` inside the handshake, and the seam value
    builds the `SecureConn` only when it accepted the peer's
    certificate. A refused certificate is `Core.Error.authentication`,
    with the reason of the refusal, whether the engine refused it (a
    chain of more than one, no client certificate) or `Tls.verify` did.
    The peer gets the alert `bad_certificate` for a refused
    certificate, and `certificate_required` when it was a client that
    sent none (RFC 8446 §4.4.2.4; `net/tls`, "The certificate check").
    A failed read of the wall clock is a refusal too, before the first
    byte of the handshake: the validity window cannot be checked, and
    the spec says to abort. A peer that uses no ALPN at all reads as
    `libp2p`, as the references read it over TCP (the decision "ALPN
    `libp2p` alone").
11. **The `SignedKey` decode is capped** (§5.1). A DER length takes at
    most two bytes, `maxDerLength`, and the contents come from a
    certificate the engine has already bounded.

## The libp2p TLS handshake

The TLS spec authenticates a peer through a self-signed X.509
certificate. The certificate's own key is a fresh P-256 key, and the
host key travels in the libp2p Public Key Extension
(`1.3.6.1.4.1.53594.1.1`) as a `SignedKey`: the marshaled host public
key, and the host key's signature over `libp2p-tls-handshake:` and the
certificate's SubjectPublicKeyInfo.

The work splits in three, by what each part needs:

- **The engine** is `net/tls`: TLS 1.3 only, the client certificate,
  the one-certificate chain, the ALPN name, and no server name. It
  knows no libp2p.
- **The certificate** is `Tls/Certificate.lean`, over the X.509
  helpers of the `Crypto` facade (§3.6). `Identity.issue` signs our
  certificate key with the host key and has the backend issue the
  certificate. `Tls.verify` runs the checks of the spec in order, one
  error arm per check: the parse, the missing extension, the repeated
  extension, the unknown critical extension, the self-signature, the
  validity window, the `SignedKey` decode, the public key, the
  signature, and the peer id.
- **The seam value** is `Tls/Protocol.lean`. It reads the wall clock,
  hands the engine `certificateCheck now`, the pure check over
  `Tls.verify`, and builds the `SecureConn` from the peer that check
  accepted.

The `SignedKey` codec is pure and proved: `decode_encode` states that
every value under the cap reads back from its encoding, over the
`List Nat` byte model (CLAUDE.md, "Proofs and tests"). The decoder
refuses every DER form but the shortest, and every trailing byte.

The QUIC transport (`libp2p/quic`) calls the same `Tls.verify` on the
certificate its own handshake receives, inside that handshake, and
issues its certificate with the same `Identity`. After the handshake
it reads the peer with `Tls.identity`.

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
- **The transport runs one loop, and credits bound its read side**
  (§3.3, PRINCIPLES 3.4). A reader task, a loop task that owns the two
  cipher states, and a writer task run each secure connection, as the
  yamux shell runs a session. Noise has no window, so the loop cannot
  hold the overflow of a slow reader. The reader takes a credit before
  each post instead, and each post settles to one delivery or one
  returned credit (`stepBytesSettles`). A post holds every whole frame
  the reader has gathered, so a peer whose bytes arrive one per read
  costs one loop step per frame (the module doc of
  `Libp2p/Security/Transport.lean`, "The reader's frames"). The inbox holds
  `inboxChunks` = 1 chunk: rust-libp2p holds one decrypted frame ahead
  of its reader (`Output.recv_buffer`,
  `vendor/rust-libp2p/transports/noise/src/io.rs`, lines 42 and 73 to
  94), and nim-libp2p decrypts on the reader's demand (`readMessage`,
  `vendor/nim-libp2p/libp2p/protocols/secure/noise.nim`, line 450). The loop never parks, writes keep their nonce order
  without a lock, and TCP carries the back-pressure to the peer.
- **The responder drops the payload of message 0.** The spec puts the
  libp2p payload in the second and third messages ("XX") and says
  nothing of a payload in the first. The upstreams disagree: go-libp2p
  (`runHandshake`, `vendor/go-libp2p/p2p/security/noise/handshake.go`),
  js-libp2p (`performHandshakeResponder`,
  `vendor/js-libp2p/packages/connection-encrypter-noise/src/performHandshake.ts`),
  and nim-libp2p (`handshakeXXInbound`,
  `vendor/nim-libp2p/libp2p/protocols/secure/noise.nim`, line 411) read
  it and drop it, and rust-libp2p (`recv_empty`,
  `vendor/rust-libp2p/transports/noise/src/io/handshake.rs`, line 203)
  refuses one that decodes to any field. We follow go, the peer of the interop gate
  (W5.9); rust's refusal is the outlier. The initiator sends an empty
  payload in message 0, so a rust peer accepts it.
- **No rekey.** The spike had none, and the vendored noise-libp2p spec
  (r5) defines none. Each transport cipher state runs its counter
  toward 2^64 − 1 nonces and never reaches them in a session's life.

### TLS

- **The certificate check runs inside the handshake, as go-libp2p's
  does.** go-libp2p checks in `VerifyPeerCertificate`
  (`vendor/go-libp2p/p2p/security/tls/crypto.go`, lines 119 to 154),
  and Go sends `bad_certificate` when it fails. The engine runs
  `Tls.verify` from libssl's verify callback, which sends the same
  alert (`net/tls`, "The certificate check"). RFC 8446 §6.2 asks for
  the alert ("SHOULD send an appropriate fatal alert").
- **The expected peer id is the upgrader's check, after the
  handshake; go checks it inside.** go-libp2p's `VerifyPeerCertificate`
  also compares the derived peer id with the one the dialer intended
  (`crypto.go`, lines 143 to 149), so a dial to the wrong peer fails
  the handshake, and the server reads the alert. Here the engine's
  check takes no expected id. Root §4.9 puts the identity check in the
  upgrader, between the security and the muxer stages, as for Noise
  (contract 4). So a dial to the wrong peer finishes the TLS
  handshake, and the upgrader refuses it with `authentication`. The
  upgrader closes the secure connection through the seam
  (`discardSecure`), and the seam's close sends `close_notify`. So the
  server reads an orderly end where go's would read `bad_certificate`.
  The spec asks only that
  the client "MUST verify that the peer ID derived from the
  certificate matches", and both places do that before any
  application byte.
- **The `SignedKey` decoder refuses trailing bytes; go's does not.**
  go-libp2p reads the value with `asn1.Unmarshal` and drops what
  follows it (`crypto.go`, line 191). The spec defines the value as
  one DER `SEQUENCE`, every implementation writes it with a DER
  encoder, and the four spec certificates hold no trailing byte. So
  the strict rule refuses no real certificate, and it keeps one parse
  per value (PRINCIPLES 2.1).
- **The validity window includes both ends, and the caller gives the
  time.** The spec: "an endpoint MUST check these conditions and abort
  the connection attempt if (a) the presented certificate is not yet
  valid, OR (b) if it is expired". The spike checked the window in its
  shim, against the process clock, with both ends outside it
  (`cert_valid_now` on the `spike` branch, `c/p2pcrypto.c`).
  `Tls.verify` takes the time as an argument, and both NotBefore and
  NotAfter belong to the window (RFC 5280 §4.1.2.5). It refuses a time
  before NotBefore and a time after NotAfter. The suite pins both ends
  to the second (the unit 2 milestones).
- **The wall clock is a seam of its own.** The validity times are
  calendar times, and the `Clock` seam of §3.1 is monotonic. So
  `Tls.Config.now` reads the wall clock, and a test fixes it. The value
  reads it once, before the first byte of the handshake, since the
  check inside the handshake is a pure function (`net/tls`, "The
  certificate check"); the handshake's deadline bounds how far the
  time lies from the certificate's arrival. A failed read refuses the
  peer before the handshake, with a detail that names the clock.
- **ALPN `libp2p` alone, and the muxer from multistream-select.** The
  spec allows muxer ids in the client's ALPN offer ("Inlined Muxer
  Negotiation"). A muxer chosen there would skip the upgrader's muxer
  stage, and the upgrader imports no implementation (§2, §9 delta 10).
  So this value offers `libp2p` alone, as it advertises no muxer in
  the Noise payload. go-libp2p offers its muxers and `libp2p`, and its
  server takes `libp2p` from our offer
  (`vendor/go-libp2p/p2p/security/tls/transport.go`, lines 65 to 123).
  `scripts/tls-interop.sh` checks that no inlined muxer is chosen in
  either direction. A peer that uses no ALPN reads as `libp2p` too.
  The spec asks a server to abort only when it supports none of the
  offered protocols, which libssl does (`net/tls`, the settings), and
  the references accept a missing ALPN over TCP: Go's `crypto/tls`
  in both roles (`checkALPN` and `negotiateALPN`), rustls under
  rust-libp2p in both roles (`process_alpn_protocol`, and the server's
  `NoApplicationProtocol` only on a failed overlap), and js-libp2p's
  client, which reads no `alpnProtocol` as no early muxer. Go and
  rustls require ALPN for QUIC alone, by RFC 9001 §8.1, and
  nim-libp2p runs TLS inside QUIC only.
- **The extension is non-critical**, as go-libp2p marks it
  (`extensionCritical`, `crypto.go`, line 30). The spec allows both,
  and the suite checks that a critical one is accepted.
- **The test value fixes the keys and the wall clock.** libssl draws
  the handshake randomness, and the backend draws the certificate's
  serial number and its ECDSA nonce, so no handshake byte repeats.
  `Tls.fixedKeyProtocol` takes a fixed host key, a fixed certificate
  key, and a fixed time, so the peer ids and every validity answer
  repeat, which is what a suite above the transport predicts. The
  suites above the transport run on Noise's fixed-key value (§3.1).

## What the package must not depend on

- Inside libp2p, `core` and `identity` only (§2: identity → core →
  security). The `SecureConn` inputs and the error target come from
  `core`; the payload's key checks and the `PeerId` derivation come
  from `identity`. No import of `libp2p/negotiate`, `libp2p/mux`,
  `libp2p/host`, or `libp2p/protocols`. The modules import the core
  submodules they name: `Role`, `ProtocolId`, and `Security`.
- Crypto reaches the package through the `Crypto` facade only (§3.6):
  SHA-256, HKDF, X25519, and ChaCha20-Poly1305 for Noise, and the
  P-256 key, the X.509 helpers (`inspect`, `selfSigned`, `issue`) for
  TLS. No `crypto/backend` and no `crypto/pure` import.
- From the net group, `net/tls`: the TLS 1.3 engine, which the TLS
  value calls as `_root_.Tls` (its namespace is `Tls`, and this
  package's TLS namespace is `Libp2p.Security.Tls`). The signature
  checks go through the sign and verify dispatch of `libp2p/identity`.
- From `net/streams`, `Connection`, `BufReader` and `Framing.read` for
  the handshake reads, and `Completions` for the write tags of the
  transport shell. The shell's reader is its own task, since it posts
  whole frames (the module doc of `Libp2p/Security/Transport.lean`,
  "The reader's frames"). From `base/conc`,
  `Async`, and the channels, the cell, and the task set of that shell.
  From `base/bytes`, the byte model and `Blob`, the bytes inside core
  data. From the codec group, `codec/proto` for the payload message.
  The handshake
  signature of §4.9 names `Connection`, and core defines no re-export
  for it, so this package imports `net/streams` directly and records
  the import here, per the core pair's rule. The direction is the
  group-legal one (§2: libp2p → net).
- No knowledge of multistream-select, yamux, or mplex bytes. The
  negotiation hands this package bytes through the leftover argument,
  and the handshake consumes them without knowing what produced them.
