import TlsNative
import Tls.Error

/-!
# The TLS context

`Tls.Context` holds the settings that every session of one identity
shares: the certificate, its private key, and the one ALPN protocol.
The shim fixes the rest (`native/c/tls_shim.c`): TLS 1.3 only, no
session tickets, no session cache, no middlebox compatibility mode,
and the verify callback with its one-certificate rule (the package
ARCHITECTURE, "The settings").

The QUIC transport (W4.4, etheorem/leanp2p#92) is to run its
handshake on the same context (`Context.native`), so the TLS settings
have one home for both transports (the package ARCHITECTURE, "One
context for both transports").
-/

set_option autoImplicit false

namespace Tls

/-- The shared settings of the sessions of one identity. -/
structure Context where
  /-- The libssl context, for a shim that runs its own handshake on it
  (`native/c/tls_shim.h`). -/
  native : TlsNative.Context

/-- A context for the DER certificate `cert`, its DER private key
`key`, and the ALPN protocol `alpn`. `.error .context` when the
certificate or the key does not load, when they do not match, or when
`alpn` is empty or longer than 255 bytes. -/
def Context.new (cert key : ByteArray) (alpn : String) : IO (Except Error Context) := do
  match ← TlsNative.contextNew cert key alpn with
  | some native => return .ok ⟨native⟩
  | none => return .error .context

end Tls
