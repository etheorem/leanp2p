import Quic.Constants
import Quic.Error
import Quic.Address
import Quic.View
import Quic.Loop
import Quic.Endpoint

/-!
# Quic

The `net/quic` package: the QUIC transport (RFC 9000) over UDP, through
the pinned ngtcp2 and the shim of `native/` (root ARCHITECTURE §4, "FFI
first"). The TLS 1.3 handshake runs on a `Tls.Context` of `net/tls`,
with the caller's certificate check inside it. The package knows no
protocol above QUIC: the caller names the ALPN protocol through the
context, and gives the check. The package docs live under `docs/`
beside this file.
-/
