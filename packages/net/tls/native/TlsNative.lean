/-!
# The libssl bindings

The `@[extern]` declarations of `c/tls_shim.c`. The shim runs a TLS 1.3
endpoint over two memory BIOs: the caller feeds the bytes it read from
the peer, and drains the bytes for the peer. `Tls` (the package root)
builds the handshake and the secure connection on these calls. No
caller outside `net/tls` imports this module.

**Objects.** `Context` holds one `SSL_CTX`: the certificate, its key,
TLS 1.3 only, no session tickets, no middlebox compatibility mode, the
ALPN name, and the verify callback with its one-certificate rule. `Session` holds one `SSL`, its two BIOs, and the
caller's certificate check. Both are external objects, so the runtime
frees them when the last reference goes. A session holds a reference
to its context and to its check.

**The check runs inside the handshake.** libssl's verify callback calls
the session's check with the DER of the peer's one certificate, inside
`handshakeStep`. The check is a pure function, `ByteArray → Option
String`: the shim applies it with `lean_apply_1` and reads an ordinary
`Option` object back, so the call depends on no calling convention of
`IO`. `none` accepts, and `some reason` refuses, with `reason` as the
error text of the failed step.

**Ownership.** The shim borrows every argument (`@&`), as the backend
shim does (PRINCIPLES 4.1). Every call runs in `IO`: a session is
mutable state, and the handshake draws randomness.

**Threads.** One mutex guards each session, so the reader task and the
writer task of one connection may call at the same time. The calls
take the lock for their whole length.
-/

set_option autoImplicit false

namespace TlsNative

/-- The carrier of a `Context`. The standard pattern of an opaque FFI
type: a `NonemptyType` whose `type` field is the type. -/
opaque ContextPointed : NonemptyType

/-- One TLS context: an `SSL_CTX` with a certificate, its key, and the
ALPN name. -/
def Context : Type := ContextPointed.type

instance : Nonempty Context := ContextPointed.property

/-- The carrier of a `Session`. -/
opaque SessionPointed : NonemptyType

/-- One TLS endpoint: an `SSL` over two memory BIOs. -/
def Session : Type := SessionPointed.type

instance : Nonempty Session := SessionPointed.property

/-- The answer of one read, as C lays it out: the object field, then
the scalar. -/
structure ReadRaw where
  bytes : ByteArray
  code : UInt8

/-- A context for the DER certificate `cert` and the DER private key
`key`, with the one ALPN protocol `alpn`. `none` when the certificate
or the key does not load, when they do not match, or when `alpn` is
empty or longer than 255 bytes. -/
@[extern "leanp2p_tls_context_new"]
opaque contextNew (cert : @& ByteArray) (key : @& ByteArray) (alpn : @& String) :
  IO (Option Context)

/-- Append the DER certificate `cert` to the chain the context sends
after its own certificate. A context that holds one sends a chain of
two, which a peer must refuse ("Endpoints MUST abort the connection
attempt if more than one certificate is received"). The suites check
that rule with it; no production value sends a chain. `false` when the
certificate does not load. -/
@[extern "leanp2p_tls_context_add_chain"]
opaque addChainCertificate (context : @& Context) (cert : @& ByteArray) : IO Bool

/-- A session on `context`: the server role when `server` holds. The
server requires a client certificate. The client offers the ALPN name
and sends no server name. `check` gets the DER of the peer's one
certificate during the handshake, and `some reason` refuses it with the
alert `bad_certificate`. `none` on a library fault. -/
@[extern "leanp2p_tls_session_new"]
opaque sessionNew (context : @& Context) (server : Bool) (check : @& (ByteArray → Option String)) :
  IO (Option Session)

/-- Feed the bytes that the peer sent. `false` when the input buffer
refused them (an allocation failed); `lastError` says why, and the
session's record stream is then broken. -/
@[extern "leanp2p_tls_session_feed"]
opaque feed (s : @& Session) (bytes : @& ByteArray) : IO Bool

/-- One handshake step: 0 done, 1 more input needed, 2 failed, 3 failed
because the peer's certificate was refused (a chain of more than one,
the session's check, or a client that sent none). -/
@[extern "leanp2p_tls_session_handshake"]
opaque handshakeStep (s : @& Session) : IO UInt8

/-- Read up to `max` bytes of plaintext. The code: 0 bytes, 1 more
input needed, 2 the peer's `close_notify`, 3 failed. -/
@[extern "leanp2p_tls_session_read"]
opaque read (s : @& Session) (max : USize) : IO ReadRaw

/-- Encrypt the plaintext into the output. `false` on a failure. -/
@[extern "leanp2p_tls_session_write"]
opaque write (s : @& Session) (bytes : @& ByteArray) : IO Bool

/-- True when the session holds part of a record: at the end of the
connection, a cut record. -/
@[extern "leanp2p_tls_session_partial"]
opaque partialRecord (s : @& Session) : IO Bool

/-- Queue a KeyUpdate that asks the peer to update its keys too, and
write it to the output. `false` on a failure. -/
@[extern "leanp2p_tls_session_key_update"]
opaque keyUpdate (s : @& Session) : IO Bool

/-- Queue the `close_notify` alert in the output. -/
@[extern "leanp2p_tls_session_shutdown"]
opaque shutdown (s : @& Session) : IO Unit

/-- Take every byte that waits for the peer. -/
@[extern "leanp2p_tls_session_drain"]
opaque drain (s : @& Session) : IO ByteArray

/-- The peer's certificate as DER, once the handshake has seen it. -/
@[extern "leanp2p_tls_session_peer_certificate"]
opaque peerCertificate (s : @& Session) : IO (Option ByteArray)

/-- The ALPN protocol that the handshake selected; empty when none. -/
@[extern "leanp2p_tls_session_alpn"]
opaque alpn (s : @& Session) : IO String

/-- The negotiated protocol version text, such as `TLSv1.3`. -/
@[extern "leanp2p_tls_session_version"]
opaque version (s : @& Session) : IO String

/-- The text of the session's last failure. -/
@[extern "leanp2p_tls_session_error"]
opaque lastError (s : @& Session) : IO String

end TlsNative
