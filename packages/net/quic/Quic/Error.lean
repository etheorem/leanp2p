/-!
# The error of `net/quic`

`Quic.Error` is the one error inductive of the package (root
ARCHITECTURE §3.5). A protocol failure of a connection is a value, and
a fault of the socket stays an `IO.Error`. Each way a connection can
end has its own arm, the same closed set as the end events of the shim
(`QuicNative.EventKind`), so a caller tells a refused certificate from
a timeout or the peer's close without reading text.
-/

set_option autoImplicit false

namespace Quic

/-- Why a QUIC operation failed. -/
inductive Error where
  /-- The address is no `quic-v1` multiaddr, or the shim did not take
  it. -/
  | address
  /-- The endpoint could not start: the crypto glue failed. -/
  | endpoint
  /-- An application close with a nonzero error code, ours or the
  peer's (RFC 9000 §10.2). -/
  | closed (code : UInt64) (detail : String)
  /-- Our TLS refused the peer's certificate inside the handshake: the
  caller's check, the one-certificate rule, or a client that sent none.
  The text names the reason. -/
  | refused (detail : String)
  /-- We closed on a transport error: a protocol error of the peer, a
  TLS failure other than a refused certificate, no ALPN (RFC 9001
  §8.1), or our own refusal with CONNECTION_REFUSED (a full accept
  queue, a listener's close). `code` is the transport error we sent. -/
  | failed (code : UInt64) (detail : String)
  /-- The peer closed on a transport error; `code` is its error. A
  refusal of our certificate arrives here, as the error 0x100 plus the
  peer's TLS alert (RFC 9001 §4.8). -/
  | peerFailed (code : UInt64) (detail : String)
  /-- The handshake did not finish within its deadline (root §5.4). -/
  | timeout
  /-- The idle timer ended the connection (RFC 9000 §10.1). -/
  | idle
  /-- The connection ended with no CONNECTION_CLOSE: the peer's
  stateless reset (RFC 9000 §10.3), or a drop that ngtcp2 asked for. -/
  | dropped (detail : String)
  /-- The endpoint ended while the operation waited. -/
  | ended
  deriving BEq, Repr

/-- The error as text, for a log line. -/
def Error.toString : Error → String
  | .address => "quic: the address is no quic-v1 multiaddr"
  | .endpoint => "quic: the endpoint could not start"
  | .closed c d => s!"quic: the connection was closed with the application error {c}: {d}"
  | .refused d => s!"quic: the peer's certificate was refused: {d}"
  | .failed c d => s!"quic: we closed the connection with the transport error {c}: {d}"
  | .peerFailed c d => s!"quic: the peer closed the connection with the transport error {c}: {d}"
  | .timeout => "quic: the handshake timed out"
  | .idle => "quic: the connection was idle too long"
  | .dropped d => s!"quic: the connection was dropped: {d}"
  | .ended => "quic: the endpoint has ended"

instance : ToString Error := ⟨Error.toString⟩

end Quic
