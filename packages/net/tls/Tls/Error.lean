/-!
# The error of `net/tls`

`Tls.Error` is the one error inductive of the package (root
ARCHITECTURE §3.5). A protocol failure of the engine is a value. A
fault of the connection under it stays an `IO.Error`. The arms that
come from libssl carry its error text, so a log shows the cause that
OpenSSL names.
-/

set_option autoImplicit false

namespace Tls

/-- Why a TLS operation failed. -/
inductive Error where
  /-- The certificate or the key did not load, they do not match, or
  the ALPN name is empty or longer than 255 bytes. -/
  | context
  /-- The library could not make a session: an allocation failed. -/
  | session
  /-- The handshake failed. The text is libssl's. A version below TLS
  1.3, no common ALPN protocol, and an alert from the peer land here. -/
  | handshake (detail : String)
  /-- The peer's certificate was refused inside the handshake: the peer
  sent a chain of more than one certificate, the caller's check refused
  it, or a client sent none. The text names the reason: the check's own
  for its refusal, the shim's for a chain, and libssl's for a missing
  client certificate. -/
  | peerCertificate (detail : String)
  /-- The peer closed the connection before the handshake was done. -/
  | closed
  /-- The handshake completed with no peer certificate. The server
  requires one, so only a fault reaches this arm. -/
  | noCertificate
  /-- A record of the secure connection failed: a bad tag, a bad
  alert, or a failed write. The text is libssl's. -/
  | record (detail : String)
  deriving BEq, Repr

/-- The error as text, for a log line. -/
def Error.toString : Error → String
  | .context => "tls: the certificate, the key, or the ALPN name did not load"
  | .session => "tls: the library could not make a session"
  | .handshake d => s!"tls: the handshake failed: {d}"
  | .peerCertificate d => s!"tls: the peer's certificate was refused: {d}"
  | .closed => "tls: the peer closed the connection during the handshake"
  | .noCertificate => "tls: the peer sent no certificate"
  | .record d => s!"tls: a record failed: {d}"

instance : ToString Error := ⟨Error.toString⟩

end Tls
