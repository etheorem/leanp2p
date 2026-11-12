# leanp2p tls: architecture

`net/tls` runs TLS 1.3 over a `Streams.Connection`. It binds libssl,
the TLS half of OpenSSL 3, through a small C shim behind a Lean
interface, the FFI-first path of root ARCHITECTURE §4 ("FFI first,
Lean later"; PRINCIPLES 4.1). The package knows no protocol above TLS
(§2; PRINCIPLES 4.3). The caller names the one ALPN protocol, gives the
certificate and its key, and gives the check of the peer's certificate,
which the engine runs inside the handshake. The libp2p TLS handshake
(`libp2p/security`, root PLAN W5.11) is its caller, and the QUIC
transport (W4.4, etheorem/leanp2p#92) is to be the second.

## Modules

| Module | Holds, and why |
|---|---|
| `native/c/tls_shim.c` | the shim: one context (`SSL_CTX`) and one session (`SSL` over two memory BIOs) as external objects, each call under the session's mutex |
| `native/c/tls_shim.h` | the five C entries for another shim: the `SSL_CTX` and the ALPN list of a context object, the attach of a certificate check to an `SSL` of that context, the reason of its refusal, and the test that a failed step refused the peer's certificate |
| `native/TlsNative.lean` | the `@[extern]` declarations of the shim, one per exported function |
| `native/lakefile.lean` | the nested Lake package that compiles the shim (PRINCIPLES 4.2) |
| `Tls/Constants.lean` | the record size of TLS 1.3 and the bound of the `close_notify` write, one home each (§3.8) |
| `Tls/Error.lean` | `Tls.Error`, the one error inductive of the package (§3.5) |
| `Tls/Context.lean` | `Tls.Context`: the certificate, the key, and the ALPN name that every session of one identity shares |
| `Tls/Conn.lean` | `Tls.handshake` and the secure connection it answers, `Tls.Secured` |
| `Tls.lean` | the package root, one import line per submodule |

## Public surface

- `Tls.Context.new cert key alpn : IO (Except Error Context)`: a
  context for a DER certificate, its DER private key, and one ALPN
  protocol.
- `Tls.handshake ctx server conn leftover check clock : Async (Except
  Error Secured)`: the handshake in the server role when `server`
  holds, and the client role otherwise. `leftover` holds the bytes the
  negotiation read past its last message (§4.7). `check : ByteArray →
  Option String` decides the peer's certificate inside the handshake:
  `none` accepts, and `some reason` refuses ("The certificate check").
  `clock` (default `Clock.system`) bounds the `close_notify` write of
  the secure connection.
- `Tls.Secured`: the secure `connection`, the peer's certificate (DER)
  that the check accepted, the selected ALPN protocol, `keyUpdate`
  (a TLS 1.3 KeyUpdate that asks the peer to update its keys too),
  `abort` (a close with no alert), and `join`.
- `Tls.Context.native`, the libssl context object, which a QUIC shim
  hands to its own code ("One context for both transports").

## The engine

The shim opens no socket, starts no thread, and reads no clock. An
`SSL` reads from one memory BIO and writes to another. `Tls/Conn.lean`
moves the bytes: a connection read goes into the input BIO, and the
output BIO goes to the connection. The handshake loop runs one
`SSL_do_handshake` step, writes the step's output, and reads the
connection only when the step asks for more input. The step's output
goes out before the read, so the peer's next flight can come.

Every byte goes into the engine, the bytes the negotiation over-read
included. So the engine holds whatever the handshake read past its
last message, and decrypts it at the next read. The hand-over of §4.7
happens inside the engine, and `Secured` has no leftover field.

## The settings

`Tls.Context.new` fixes the settings that the libp2p TLS spec asks for
(`vendor/specs/tls/tls.md`):

| Setting | The shim | The spec |
|---|---|---|
| TLS 1.3 only | `SSL_CTX_set_min_proto_version` and `max` at `TLS1_3_VERSION` | "Endpoints MUST NOT negotiate lower TLS versions" |
| The server requires a client certificate | `SSL_VERIFY_PEER` with `SSL_VERIFY_FAIL_IF_NO_PEER_CERT` on the server's `SSL` | "servers MUST require client authentication" |
| One certificate in the chain | the verify callback refuses a chain of more than one | "Endpoints MUST abort the connection attempt if more than one certificate is received" |
| The caller checks the certificate | the verify callback runs the caller's check on the one certificate | the libp2p checks need the identity package (the next section) |
| One ALPN protocol | the client offers it; the server selects it or refuses the handshake, and a client that offers no ALPN at all gets none | "The server MUST abort the handshake if it doesn't support any of the application protocols offered by the client" |
| No server name | the client sets none | "clients … MUST NOT send any value in the Server Name Indication" |
| No session tickets, no session cache | `SSL_OP_NO_TICKET`, `num_tickets` 0, `SSL_SESS_CACHE_OFF` | a resumed session would skip the certificate the peer proves its key with |
| No middlebox compatibility mode | `SSL_OP_ENABLE_MIDDLEBOX_COMPAT` cleared | RFC 8446 Appendix D.4 makes the mode optional. In it the libssl client keeps its write side in plaintext until its second flight (`statem_clnt.c`), so the alert of a refused server certificate arrives unencrypted, and Go's server, which reads the client handshake key from ServerHello on (`handshake_server_tls13.go`, `sendServerParameters`), cannot read it. `scripts/tls-interop.sh` checks the alert against go. |

## The certificate check

libssl calls the shim's verify callback in place of its own chain
verification (`ssl_verify_internal`, `ssl/ssl_cert.c`). The callback
enforces the one-certificate rule, since only it sees the chain. Every
other check needs the libp2p key types and peer ids, which live above
this package (§2), so the callback then runs the caller's check on the
certificate's DER. go-libp2p makes the same split: Go's `crypto/tls`
skips its chain verification (`InsecureSkipVerify`), and the transport
checks the certificate inside the handshake (`VerifyPeerCertificate`,
`vendor/go-libp2p/p2p/security/tls/crypto.go`, lines 92 and 119 to
154).

A refusal sets `X509_V_ERR_CERT_REJECTED`, which libssl sends as the
alert `bad_certificate` (`ssl_x509err2alert`, `ssl/statem/statem_lib.c`),
the alert Go sends when `VerifyPeerCertificate` fails
(`crypto/tls/handshake_client.go` and `handshake_server.go`). The
handshake then fails with `Error.peerCertificate`, whose text is the
reason the check gave. The shim tells these refusals apart from the
other handshake failures by the verify result, and a client with no
certificate by libssl's reason `SSL_R_PEER_DID_NOT_RETURN_A_CERTIFICATE`
(`tls_process_client_certificate`). That client gets the alert
`certificate_required` instead, the alert RFC 8446 §4.4.2.4 names for a
server that aborts on a missing client certificate.

The check is a pure function, `ByteArray → Option String`. The shim
calls it with `lean_apply_1` and reads an ordinary `Option` object
back, so the call depends on no calling convention of `IO`. A caller
that needs the time reads it before the handshake and builds the check
from it.

## One context for both transports

QUIC runs TLS 1.3 inside its own packets (RFC 9001). The QUIC
transport (W4.4, etheorem/leanp2p#92) is to drive an `SSL` from its
own shim, and that `SSL` comes from the same `SSL_CTX`. The TLS
settings of the table above then have one home for both transports
(PRINCIPLES 1.5). `tls_shim.h` gives that shim what it needs:

- the context and the ALPN list of a `Tls.Context` object;
- `leanp2p_tls_attach_check`, which hands its `SSL` the caller's
  check. The context's verify callback finds the check in the `SSL`'s
  ex_data, and an `SSL` with no check refuses every certificate,
  fail-closed. A session attaches its own check the same way, so both
  transports reach the check through one path;
- `leanp2p_tls_refusal` and `leanp2p_tls_refused`, which tell a
  refused certificate from another failed step and give its reason,
  as the session's handshake step does.

The `SSL` owns its check: the ex_data slot's free callback drops the
check's reference in `SSL_free`.

## The order of the records

The secure read and the secure write run on two tasks: the muxer's
reader and its writer. libssl allows one thread on an `SSL` at a time,
so one mutex guards each session, and every shim call takes it for its
whole length. Two calls still reach the connection through two writes,
and a reordered pair breaks the record sequence. So one write token
orders the output (`Tls/Conn.lean`, "The order of the records"): a task
writes the session's output only while it holds the token, and the
output BIO is first in, first out. A read that succeeds leaves no
output: libssl answers a KeyUpdate before its next application data
record (`ssl3_write_bytes`, `ssl/record/rec_layer_s3.c`), as RFC 8446
§4.6.3 allows. So only writers use the token, and a held token is a
write in flight. A failed read sends its fatal alert when the token is
free.

## Owned contracts

1. **TLS 1.3 only, a client certificate, one certificate, one ALPN
   protocol, no server name** (the settings table). The shim fixes
   them, and no caller can loosen them.
2. **No application byte before the caller's check.** The check runs
   inside the handshake, and `Tls.handshake` answers a `Secured` only
   when it accepted the peer's certificate.
3. **A failed record is a protocol error, distinct from EOF** (§3.5;
   PRINCIPLES 2.4). The secure read sends the fatal alert, records the
   error, closes the connection, and answers `none`. `Secured.join`
   answers it. An end of the connection inside a record is a failed
   record; an end at a record boundary is an orderly end.
4. **A write fails loud** (§4.7). A failed write sends the fatal alert,
   records the error, closes the connection, and throws.
5. **Every park has a close** (PRINCIPLES 3.1). A handshake read and a
   secure read park on the connection, which the caller's deadline or
   `close` closes. A writer parks on the write token, which `close`
   closes. The `close_notify` write is bounded by `closeNotifyMs`.
6. **Every task has an owner** (PRINCIPLES 3.2). The one task of a
   secure connection sends the `close_notify` alert, and
   `Secured.join` joins it.
7. **The shim borrows every argument** (PRINCIPLES 4.1), and a session
   holds a reference to its context, so the `SSL_CTX` outlives every
   `SSL` of a session. An `SSL` holds one reference to its check, which
   `SSL_free` drops.

## Decisions

- **A package of its own, in the net group.** TLS is a transport
  security layer over a byte stream, as the yamux session is a muxer
  over one, and two callers above it share it. The libp2p certificate
  logic stays in `libp2p/security`, so this package keeps rule 2 of
  the import lint.
- **Memory BIOs, and the bytes in Lean.** The connection is a seam
  (§3.1), so the sim transport carries TLS in the suites the same way
  TCP does. A socket BIO would bind the engine to a file descriptor.
- **The check runs inside the handshake, so a refusal sends
  `bad_certificate`.** RFC 8446 §6.2: on a fatal error an
  implementation "SHOULD send an appropriate fatal alert and MUST close
  the connection without sending or receiving any additional data".
  libssl sends an alert for a refusal of its verify callback alone, so
  the caller's check runs there, as go-libp2p's runs inside Go's
  handshake ("The certificate check").
- **`close` sends `close_notify`, by Go's rules.** RFC 8446 §6.1: "Each
  party MUST send a "close_notify" alert before closing its write side
  of the connection". Go's `Close` sends no alert while a `Write` is in
  flight, since that close breaks the write (`crypto/tls`, `conn.go`,
  `Close`). Here the close takes the token with no wait, and a held
  token is a write in flight, so the rule is the same, and the alert
  never lands between the records of one write. The write of the alert
  has the bound `closeNotifyMs`, 5 seconds, as Go's `closeNotify` sets.
- **`abort` sends no alert.** A caller that refuses the peer after the
  handshake closes "without sending or receiving any additional data"
  (§6.2). The libp2p value has no such refusal of a well-behaved peer:
  it uses `abort` only on its fail-closed fault arms. libssl's public
  API has no call that sends an alert of the caller's choice (`ssl.h`
  declares only the `SSL_alert_*_string` lookups), so the alert §6.2
  says the close SHOULD send stays unsent there.
- **The end of the connection, by Go's rule.** Go reads an end at a
  record boundary as the end, even with no `close_notify`, and an end
  inside a record as `io.ErrUnexpectedEOF` (`crypto/tls`, `conn.go`,
  `readRecordOrCCS`). libssl cannot tell the two apart: with
  `SSL_OP_IGNORE_UNEXPECTED_EOF` it takes every end, and without it
  none (`ssl/record/rec_layer_s3.c`). So the shim reports the bytes of
  a record it has not read whole (`SSL_has_pending`, and the input
  BIO), and the secure read applies Go's rule.
- **A KeyUpdate in both directions.** `Secured.keyUpdate` asks the peer
  to update its keys too (RFC 8446 §4.6.3), through `SSL_key_update`
  and `SSL_do_handshake`. libssl answers a peer's request from its next
  write, "prior to sending its next Application Data record".
- **No world argument in a C binding.** Lean v4.34 calls an `IO`
  extern with its declared arguments alone and reads an IO result back
  (the prototypes and call sites in `.lake/build/ir`). So no shim
  function takes the world token.
- **The libssl of the toolchain.** The shim compiles against the
  system OpenSSL 3 headers and links the static `libssl.a` that the
  Lean toolchain bundles (3.6.0 on v4.34.0), as `crypto/backend` links
  its `libcrypto.a`. `lean-toolchain` pins the runtime library, and a
  second OpenSSL never enters the process.

## What the package must not depend on

- Nothing of the libp2p group, and no mention of it in a `.lean` file
  (§2; the import lint, rule 2).
- From the net group, `net/streams` only: `Connection`.
- From `base`, `base/conc`: `Async`, `Chan`, `OnceRef`, `TaskSet`,
  `Clock`, and `withinDeadline`.
- No crypto import: libssl brings its own primitives, and the caller's
  certificate check goes through the `Crypto` facade above this
  package.
