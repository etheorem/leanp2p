# leanp2p libp2p quic: architecture

`libp2p/quic` is the QUIC transport of libp2p (the QUIC spec,
`vendor/specs/quic/README.md`) as a `SecuredTransport` value of
`libp2p/core` (root ARCHITECTURE §4.9). The QUIC engine is `net/quic`.
The TLS side is the libp2p TLS handshake of `libp2p/security`: the
same `Tls.Config` issues our certificate and holds the engine context
with the ALPN `libp2p`, and the same checks decide the peer's
certificate. The consensus networking spec makes QUIC a MUST and the
primary transport, secured with the libp2p TLS handshake
(`vendor/consensus-specs/specs/phase0/p2p-interface.md`, lines 154 to
161 and 179 to 180).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Quic.lean` | the root module; one import line per public submodule |
| `Libp2p/Quic/Constants.lean` | the numbers the value adds to the engine's: `protocolViolation`, the code of its own refusal after a handshake |
| `Libp2p/Quic/Transport.lean` | `Libp2p.Quic.transport`: the checks, the admission, the dial, the listener, and the muxer session over a QUIC connection |

All declarations live in the `Libp2p.Quic` namespace. The engine's
namespace is `Quic`, so this package calls it `_root_.Quic`.

## Public surface

- `Libp2p.Quic.transport cfg : SecuredTransport`, for a `Tls.Config`
  of `libp2p/security`. `handles` takes the `quic-v1` addresses of
  `net/quic`. `dial` answers a `SecuredSession` once the peer's
  certificate passed the check. It hands its `abort` channel to
  `Quic.dial`, so the close of that channel ends a dial still in its
  handshake with `closed`. `listen` answers a listener whose `accept`
  gives only the sessions that passed the checks. The engine's timers
  run on `cfg.clock`.
- `Libp2p.Quic.fixedKeyTransport key certKey now`: the test value of
  §3.1, over `Tls.Config.fixed`.
- `Libp2p.Quic.mapError`, `dialCheck`, `clockFailed`: the error map and
  the checks, public so the suite and a reader can name them.

## The check

The engine runs the check inside the handshake (`net/quic`, "The
certificate check"). A refused peer gets the alert `bad_certificate`
as CRYPTO_ERROR 0x12a (RFC 9001 §4.8), and neither side's host sees
the connection. The TLS spec's "Peer Authentication" MUSTs therefore
hold over QUIC as over TCP (the security ARCHITECTURE, contract 9).

- **A dial** reads the wall clock of `Tls.Config.now` once, before the
  handshake, as the TLS value over TCP does. Its check, `dialCheck`,
  runs `Tls.verify` at that time. With an expected peer id, it also
  compares the proved id with it, inside the handshake. The TLS spec:
  "Clients MUST verify that the peer ID derived from the certificate
  matches the peer ID they intended to connect to". go-libp2p makes
  the same comparison in its `VerifyPeerCertificate` callback, so the
  wrong peer gets the alert there too.
- **A listener** gives the engine an admission (`listenAdmit`), which
  the engine runs when a connection's first datagram arrives. The
  admission asks the owner's `Core.Admit` first: the host's gater and
  resource manager (the core ARCHITECTURE, "The secured transport
  seam"). A refusal costs the peer one CONNECTION_REFUSED and us no
  handshake, as go-libp2p's `ConnContext` refuses a connection
  (`vendor/go-libp2p/config/config.go`). An admitted connection gets
  its own check, which reads the wall clock at its own start. Its scope
  travels with it to `accept`. The engine releases the scope of a
  connection that ends in its handshake. The value releases the scope
  of one that `admit` refuses after the handshake.
- **A failed read of the wall clock** gives `clockFailed`, a check that
  refuses every certificate: the validity window cannot be checked,
  and the spec says to abort.

After the handshake, `admit` reads the peer with `Tls.identity`, every
step of `Tls.verify` but the validity window. The theorem
`Tls.identity_of_verify` states that it answers the peer the check
accepted, so its error arm cannot occur; the arm closes the
connection, fail-closed.

## The ALPN

QUIC requires ALPN (RFC 9001 §8.1; the QUIC spec, "ALPN": "QUIC
enforces the use of ALPN, so the handshake will fail if both peers
can't agree on the application protocol"). The engine closes a
connection that negotiated none. The context offers and selects
`libp2p` alone, and libssl refuses a selection we did not offer. So a
connection always carries `libp2p`, and `admit` checks it again,
fail-closed.

## The session

QUIC streams are the muxer streams (RFC 9000 §2; the consensus spec,
line 210: "the primary QUIC transport multiplexes natively"). So the
`SecuredSession`'s `MuxSession` is a thin view. `openStream` opens a
bidirectional stream and drops the protocol id, as yamux does. The
stream's protocol comes from multistream-select on the stream (the
connections spec, "Opening New Streams Over a Connection"). `close`
closes the connection with application error 0, and `join` answers its
end through `mapError`.

## The errors

`mapError` maps an engine error once into `Core.Error` (§3.5):

| Engine error | Core error | Why |
|---|---|---|
| `refused` | `authentication` | our check refused the peer's certificate |
| `failed`, `peerFailed` | `protocol` | a transport error; a peer that refused our certificate closes with CRYPTO_ERROR, as the TLS value over TCP reads the peer's alert as `protocol` |
| `timeout`, `idle` | `timeout` | a timer ended the connection |
| `closed`, `dropped`, `ended` | `closed` | the connection ended |
| `address`, `endpoint` | `protocol` | the dial could not start |

## Owned contracts

1. **No session before the check.** The host sees a connection only
   after the check accepted its certificate inside the handshake, and
   `admit` found the ALPN and the peer.
2. **One check for both transports.** The TLS value over TCP and this
   value run the same `Tls.verify` and issue with the same
   `Tls.Config` (PRINCIPLES 1.5).
3. **The errors map once** (§3.5), through `mapError`.

## Decisions

- **A seam of its own, beside `Streams.Transport`.** A QUIC connection
  arrives secured and muxed, so the upgrader has no stage to run on it.
  The `SecuredTransport` seam of `libp2p/core` carries it, and the host
  serves a `SecuredSession` as it serves an upgraded connection: the
  same checkpoints, the same dedup, the same handlers. The TCP path and
  `Streams.Transport` stay as they are. go-libp2p draws the same line
  with `CapableConn` (the core ARCHITECTURE, "The secured transport
  seam").
- **A leaf of its own, at the rank of `negotiate`.** The value imports
  `core`, `identity`, and `security`, and the host imports none of them
  (§3.1: the host imports core and no implementation). `cli/` puts the
  value into the host's configuration.
- **The check inside the handshake.** A peer refused after the
  handshake would see a finished handshake and then an application
  close. Inside it, the peer gets the TLS alert that go-libp2p sends
  for the same refusal, and the check of `libp2p/security` keeps one
  shape for both transports.

## What the package must not depend on

- Inside libp2p, `core`, `identity`, and `security` (its `Tls/`
  modules) only. No import of `negotiate`, `mux`, `host`, or
  `protocols`.
- From the net group, `net/quic`, `net/tls` (the context type of the
  configuration), and `net/streams` (`Stream`).
- From `base`, `base/conc`.
