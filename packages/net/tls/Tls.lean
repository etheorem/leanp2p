import Tls.Constants
import Tls.Error
import Tls.Context
import Tls.Conn

/-!
# Tls

The `net/tls` package: TLS 1.3 over a `Streams.Connection`, through the
libssl shim of `native/` (root ARCHITECTURE §4, "FFI first"). The
package knows no protocol above TLS. The caller names the ALPN
protocol, and the caller checks the peer's certificate. The package
docs live under `docs/` beside this file.
-/
