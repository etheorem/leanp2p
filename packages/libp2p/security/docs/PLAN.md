# leanp2p security: plan

This plan refines the root `docs/PLAN.md` for `libp2p/security`. The
root plan owns the order across packages (PLAN.md, "How to read this
plan"). Units 1a and 1b below are the root unit W5.3, with root deps
W4.2, W3.3, and W5.2. The done-when of unit 1b is the root row plus the
root definition of done: the surface follows ARCHITECTURE §4.9, shaped
by §3, the owned contracts hold, the carried vector and property tests
pass, the suite passes under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W3.3, W5.2 | the handshake core and the payload: `State`/`Event`/`Action`/`step` (§3.3), the framing codec, `NoiseHandshakePayload` with its `ProtoMessage` instance, and `Noise.Error` | the core replays the transcript milestones below with no connection in the loop |
| 1b | 1a, W4.2 | the transport and the two `SecurityProtocol` values: framed AEAD reads and writes over `SecureConn`, `Noise.securityProtocol`, the fixed-key test value, and the `Except.mapError` into `Core.Error` | the root W5.3 row holds, and the milestones below pass |

The split lets the pure side close on transcripts alone. The core needs
W3.3 for the facade and W5.2 for the `SecureConn` inputs; W4.2 gates
only the framed IO path and the seam values, which unit 1b carries.

Unit 0 is done.

## Consumers

- The upgrader (W5.5) runs the handshake inside the 30 s deadline of
  §5.4 and hands the leftover on in both directions (§4.7, §5.6).
- The host (W5.6) supplies the dial target as the expectation, and the
  upgrader (W5.5) compares the completed `remotePeer` against it (the
  negotiate pair's refinement). A failure is
  `Core.Error.authentication` (§3.5, §4.9).
- The fixed-key test value serves every suite above the transport
  (§3.1): negotiate, host, protocols, and the `cli/` binaries run over
  it instead of random keys.

## Test milestones (unit 1a)

- The flynn XX transcripts replay through the core as events in and
  actions out, in both roles. All four cases of `noise-vectors.json`
  replay: prologue empty and present, payloads empty and present, five
  messages each, three handshake messages and two transport frames.
- The go transcript replays the responder role byte-for-byte: message 2
  reproduces the captured bytes, message 3 decrypts and verifies, and
  the derived cipher states round-trip the recorded transport frames.
- The 8 KiB cap: a handshake payload one byte over is rejected before
  the decode runs (§5.2, PRINCIPLES 2.4).
- The static-key check: a payload whose signature was made over a
  different static key, or whose signature fails to verify, is an
  authentication error. The completion carries the `PeerId` the
  payload's identity key derives; the host (W5.6) supplies the expected
  id, and the upgrader compares it (the negotiate pair's refinement).

## Test milestones (unit 1b)

- The handshake completes over the sim transport end-to-end, in both
  roles, and the peers derive the expected `PeerId`s.
- The AEAD-failure and EOF distinction: a corrupted frame is a protocol
  error and tears the connection down; a clean close reports `none`
  after the teardown (PRINCIPLES 2.4). The backend pair pins the RFC
  8439 wrong-AD and wrong-nonce rejections at the binding; this
  package pins the same failure through its own reads, with a
  bit-flipped frame.
- The 64 KiB frame cap: a write above 65519 bytes of plaintext chunks
  into frames the peer reads back whole, and a read honors the cap
  before allocation (§5.1).
- The fixed-key value interoperates with itself over the sim in both
  roles, with no randomness on the path (§3.1). The test identity is
  Ed25519, whose signature is deterministic (§3.6); a secp256k1
  identity would draw a random signature nonce and break the claim.
- The leftover hand-over: bytes the negotiation over-read reach the
  handshake through the `ByteArray` argument, and bytes the handshake
  over-read reach the transport reader through the `SecureConn`
  (§4.7, §5.6).
- The suite passes under `+RTS -N1` (§6, PRINCIPLES 5.3).

## Vector stance

`noise-vectors.json` holds the flynn/noise XX vectors for
`Noise_XX_25519_ChaChaPoly_SHA256`: four cases with prologue and
payload variations, pinned in `VECTORS.lock` at the commit the lock
records. The flynn library is the exact library go-libp2p's Noise uses.
`noise-go-transcript.json` holds a captured go-libp2p v0.50.0
`Transport.SecureOutbound` handshake against a deterministic responder,
plus post-handshake transport frames. The RFC 8439 §2.8.2 vector for
ChaCha20-Poly1305 is inlined in the spike's `Tests/Noise.lean`, with
its wrong-AD and wrong-nonce rejections. All of these arrive through
W0.3, with `VECTORS.lock`, `scripts/extract-vectors.py`, and
`Tests/vectors/` (§6). The go interop matrix over `tcp + /noise +
yamux`, dial and listen, is the W5.9 gate and no gate of this package.
