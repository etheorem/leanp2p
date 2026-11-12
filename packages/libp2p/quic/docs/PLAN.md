# leanp2p libp2p quic: plan

This plan refines the root `docs/PLAN.md` for `libp2p/quic`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Unit 1 below is the libp2p half of root unit W4.4; `net/quic`
carries the engine. The done-when of the unit is the root row plus the
root definition of done: the surface follows ARCHITECTURE §4.9, the
owned contracts hold, the carried tests pass, the suite passes with
`LEAN_NUM_THREADS=1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W5.11, `net/quic` unit 1, W5.2, W5.6 | `Libp2p.Quic.transport` over the `SecuredTransport` seam, its test value, the host's secured transports, and the QUIC-first ranker | the milestones below pass, and the root W4.4 row holds |

Units 0 and 1 are done. The suite is the libp2p part of
`Tests/Quic.lean`.

## Consumers

- The host (W5.6) dials and listens through the value, from its
  `securedTransports` list, and ranks QUIC addresses first.
- `cli/` (W5.9): the harness's `quic-v1` cells.

## Test milestones (unit 1)

- A dial and an accept over loopback UDP: each side proves the other's
  peer id and names its own, a stream carries bytes, and the dialer's
  close ends both joins in order.
- A dial that expects another peer id fails with `authentication`
  inside the handshake, and the listener accepts nothing.
- A listener whose certificate expired fails the dial with
  `authentication`.
- A dialer whose certificate lacks the libp2p extension: the listener
  refuses it inside the handshake with `bad_certificate`, CRYPTO_ERROR
  0x12a (RFC 9001 §4.8), and its closed listener accepts none.
- A listener whose wall clock fails refuses every dialer, and accepts
  no session.
- The test value: fixed keys and a fixed clock prove the same peer id
  in two runs.
- The default ranker of the host puts the QUIC address first (the
  consensus spec's SHOULD).
- Two hosts over QUIC only: a dial by address and peer id, a ping that
  echoes, the server's view of the client, and both closes with no
  fault. A QUIC dial still in its handshake ends at the host's close.
- The host's secured paths over the sim value of the seam
  (`Libp2p.Negotiate.securedOver`, `Tests/Host.lean`): the pipeline,
  the ranker's choice of the QUIC address over the TCP one, a dial over
  both paths at once, the gater's refusals before and after the
  handshake with every scope released, and the close of a secured dial
  and of a secured accept in their handshakes.
- `scripts/quic-interop.sh` against go-libp2p v0.50.0's host with its
  QUIC transport (quic-go v0.62.0), in both directions. Both
  certificates and peer ids check, and the go host's identify of the
  Lean host records our agent and our protocols. A stream whose first
  proposal draws `na` echoes 2 MiB. That is past both initial windows,
  so each side sends window updates. The close is orderly. A third run
  dials a go listener that answers the first Initial with a Retry, the
  path of a go node under load (`vendor/go-libp2p/config/config.go`,
  lines 412 to 414). The dialer must take the Retry (RFC 9000
  §17.2.5.2).
- The same script checks the `tls.md` "Peer Authentication" MUSTs
  between the two sides (`scripts/quic-interop/refuse.go`), each
  refusal inside the handshake and each with its alert:
  - our listener refuses a go client with no certificate
    (`certificate_required`, RFC 8446 §4.4.2.4), one without the libp2p
    extension, and one with a chain of two (`bad_certificate`);
  - go refuses our dials with a certificate without the extension and
    with a chain of two (`bad_certificate`);
  - our dialer refuses a go server without the extension
    (`bad_certificate`), which go reads from its early listener;
  - our ClientHello names no server (SNI).
- The `quic-v1` cells of the W5.9 matrix pass: go and Lean on both
  sides (`scripts/interop-matrix.sh`; the cli PLAN, unit 3).
- The suite passes with `LEAN_NUM_THREADS=1` (PRINCIPLES 5.3).

## Vector stance

QUIC and TLS draw fresh randomness, so no transcript repeats. The
certificate checks rest on the spec vectors of `libp2p/security`
(`tls-ext.json`), and the live checks are the interop script and the
matrix cells above.
