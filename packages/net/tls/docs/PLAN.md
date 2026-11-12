# leanp2p tls: plan

This plan refines the root `docs/PLAN.md` for `net/tls`. The root plan
owns the order across packages (PLAN.md, "How to read this plan").
Unit 1 below is the engine half of root unit W5.11. The done-when of
the unit is the root row plus the root definition of done: the surface
follows ARCHITECTURE §4, the owned contracts hold, the carried tests
pass, the suite passes with `LEAN_NUM_THREADS=1`, and the import lint
is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W1.1, W4.1 | the libssl shim and its bindings, `Tls.Context`, `Tls.handshake`, and the secure connection | the milestones below pass, and the `libp2p/security` TLS suite runs on the package |

Units 0 and 1 are done. The suite is `Tests/Tls.lean`, which runs the
engine through the libp2p TLS value of `libp2p/security`, since the
certificate check that completes a handshake lives there.

## Consumers

- `libp2p/security` (W5.11): `/tls/1.0.0` over TCP runs its handshake
  and its records here, and gives the engine its certificate check.
- The QUIC transport (W4.4, etheorem/leanp2p#92), to come: its shim is
  to run its handshake on a `Tls.Context`, and to attach its check to
  each of its `SSL`s, through `tls_shim.h` ("One context for both
  transports").

## Test milestones (unit 1)

- A handshake in both roles over the sim pair, whole and with every
  write split into single bytes, with data both ways and an orderly
  close: the peer reads the end, and both joins answer `.ok`.
- A write past one record (300000 bytes, 19 records) arrives whole.
- A client that offers another ALPN name fails, and the server refuses
  the handshake (owned contract 1).
- A client certificate without the caller's extension: the server's
  check refuses it inside the handshake, and the client's first read
  ends with the alert `bad_certificate` (owned contract 2). An expired
  server certificate: the client's check refuses it, and the server's
  handshake fails on the same alert.
- A server that sends a chain of two certificates fails the client's
  handshake with `Error.peerCertificate`, and the server gets
  `bad_certificate` (owned contract 1). `TlsNative.addChainCertificate`
  makes the chain; no production value sends one.
- A KeyUpdate: the peer's read writes nothing, its next write carries
  its own KeyUpdate (one 27-byte record more than the write after it),
  and data flows both ways under the new keys.
- A record that fails to decrypt: the read ends, the reader sends the
  fatal alert, `join` answers `.record`, and the peer reads the alert
  `bad_record_mac` (owned contract 3).
- `close` writes the `close_notify` alert, one 24-byte record, and the
  peer's join answers an orderly end. `abort` writes nothing. A close while a write is
  parked on a peer that never reads writes no alert, and the parked
  write throws.
- The end of the connection at a record boundary is an orderly end; an
  end inside a record is `.record`.
- The secure connection hands no leftover on (ARCHITECTURE, "The
  engine").
- The suite passes with `LEAN_NUM_THREADS=1` (PRINCIPLES 5.3).

## Vector stance

TLS 1.3 handshakes draw fresh randomness, so no byte transcript repeats,
and the package carries no vector. The live check is the interop
check of `libp2p/security` (`scripts/tls-interop.sh`) against
go-libp2p's TLS transport over Go's `crypto/tls`, in both directions,
with the refusals and their alerts, a client with no certificate, peers
that use no ALPN, and a server that checks our client sends no server
name. The QUIC transport is to add its own interop check on the same
context.
