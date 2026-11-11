# leanp2p security: plan

This plan refines the root `docs/PLAN.md` for `libp2p/security`. The
root plan owns the order across packages (PLAN.md, "How to read this
plan"). Units 1a and 1b below are the root unit W5.3, with root deps
W4.2, W3.3, and W5.2. The done-when of unit 1b is the root row plus the
root definition of done: the surface follows ARCHITECTURE §4.9, shaped
by §3, the owned contracts hold, the carried vector and property tests
pass, the suite passes with `LEAN_NUM_THREADS=1`, and the import lint
is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W3.3, W5.2 | the handshake core and the payload: `State`/`Event`/`Action`/`step` (§3.3) over the `u16be` frame of `Streams.Framing` (ARCHITECTURE, "The core shape"), `NoiseHandshakePayload` with its `ProtoMessage` instance, and `Noise.Error` | the core replays the transcript milestones below with no connection in the loop |
| 1b | 1a, W4.2 | the transport and the two `SecurityProtocol` values: framed AEAD reads and writes over `SecureConn`, `Noise.securityProtocol`, the fixed-key test value, and the `Except.mapError` into `Core.Error` | the root W5.3 row holds, and the milestones below pass |
| 2 | W3.2, W5.1, W5.2, `net/tls` unit 1 | the libp2p TLS handshake (root W5.11): the `SignedKey` codec, `Tls.verify`, `Tls.Identity`, `Tls.securityProtocol`, and the fixed-key test value `Tls.fixedKeyProtocol` | the root W5.11 row holds, and the unit 2 milestones below pass |

The split lets the pure side close on transcripts alone. The core needs
W3.3 for the facade and W5.2 for the `SecureConn` inputs; W4.2 gates
only the framed IO path and the seam values, which unit 1b carries.

Units 0, 1a, and 1b are done: the suite is `Tests/Noise.lean`, and the
interop check of the vector stance runs through
`scripts/noise-interop.sh`. Unit 2 is done: the suite is
`Tests/Tls.lean`, and its interop check runs through
`scripts/tls-interop.sh`. The seam types come from `libp2p/core`
(W5.2).

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
- The QUIC transport (W4.4, etheorem/leanp2p#92) is to issue its
  certificate with `Tls.Identity` and check the peer's with
  `Tls.verify`, since QUIC runs the libp2p TLS handshake inside its
  own packets.

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
  authentication error. `Noise.verify` answers the `PeerId` the
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
- The suite passes with `LEAN_NUM_THREADS=1` (§6, PRINCIPLES 5.3).

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

`scripts/noise-interop.sh` runs this package alone against go-libp2p
v0.50.0's Noise transport, over loopback TCP with no negotiation, in
both directions: each side proves its peer id, 200000 bytes go each
way as four frames, and the close is orderly. It sits outside `lake
test`, as the yamux interop check does, since Go tooling stays in the
harness.

`tls-ext.json` holds the four certificates of the TLS spec ("Test
vectors"): three valid ones, with their peer ids, and one whose
`SignedKey` signature does not verify. They come through W0.3 and
`VECTORS.lock`, at the specs pin `78e75c6`, as the spike carried them.
The spike's `Tests/TlsExt.lean` checked the four through
`TlsExt.validateCert`, and unit 2 keeps those checks through
`Tls.verify`. TLS handshakes draw fresh randomness, so no handshake
transcript repeats, and the live check is
`scripts/tls-interop.sh` (unit 2 milestones).

## Test milestones (unit 2)

Unit 2 is the root unit W5.11: the libp2p TLS handshake, with the
engine of `net/tls` (that pair's unit 1). The suite is
`Tests/Tls.lean`.

- The spec vectors: each valid certificate derives the spec's peer id,
  and the invalid one fails with `CertError.signature`, as the spike
  checked them. Each `SignedKey` re-encodes to its own bytes.
- The validity window, on the first vector (NotBefore 1975, NotAfter
  4096): a time before is `notYetValid`, and a time after is
  `expired`. Both ends belong to the window: NotBefore and NotAfter
  themselves are valid, and one second outside each is refused.
- The `SignedKey` codec: `decode_encode` and `decode_encode?` are
  theorems. The suite adds a two-byte length, the cap, and the refusal
  of each non-shortest DER form, a trailing byte after the SEQUENCE and
  after the second OCTET STRING, a length past the input, and another
  outer tag.
- Our certificates, for an Ed25519, a secp256k1, an ECDSA, and an RSA
  host key: `Tls.verify` accepts each, and derives our peer id.
- One refusal per check of `Tls.verify`: bytes that are no
  certificate, a certificate without the extension, an extension that
  appears twice, an unknown critical extension (the last three over
  the generated certificates of `backend-strictness.json`), an
  extension that holds no `SignedKey`, a public key that does not
  unmarshal, a signature of another host key, and a changed signature
  byte. A critical libp2p extension is accepted.
- The handshake over the sim pair, whole and with split writes: both
  peer ids, data both ways, 300000 bytes in 19 records, no leftover,
  and an orderly close with both joins `.ok`.
- The test value: two runs of `Tls.fixedKeyProtocol` from the same
  keys and time prove the same peer ids, and the configuration keeps
  the fixed certificate key.
- The refusals of the handshake, each with its `Core.Error` class and
  what the peer sees. An expired server certificate, a client
  certificate without the extension, and a server that sends a chain
  of two certificates are `authentication`, and the peer gets the alert
  `bad_certificate`. A failed read of the wall clock is
  `authentication` before the first byte, and the peer's handshake
  reads the close. A client with another ALPN name is `protocol`: the
  server's engine refuses it. A peer that uses no ALPN at all is
  accepted, with no inlined muxer (`scripts/tls-interop.sh`, against
  go).
- The upgrade with `/tls/1.0.0` and yamux, with a stream that carries
  bytes, and an unexpected peer id, which fails the upgrade with
  `authentication`.
- `scripts/tls-interop.sh` against go-libp2p v0.50.0's TLS transport,
  over loopback TCP with no negotiation, in both directions: both
  certificates and peer ids check, 200000 bytes go each way, no
  inlined muxer is chosen though go offers yamux in ALPN, and the close
  is orderly. Four refusal runs: go dials with a certificate that lacks
  the extension and with a chain of two, and we dial a go server whose
  certificate has expired and present one without the extension to
  go-libp2p's server; each time the refusing side names its reason,
  and the other side receives the alert `bad_certificate`. Two runs
  with no ALPN, one per direction, finish the echo.
- The suite passes with `LEAN_NUM_THREADS=1` (PRINCIPLES 5.3).
