import Libp2p.Quic.Constants
import Libp2p.Quic.Transport

/-!
# Libp2p.Quic

The QUIC subpackage: QUIC as a `SecuredTransport` value (root
ARCHITECTURE §4.9), over the engine of `net/quic` and the libp2p TLS
certificate of `libp2p/security`, with its fixed-key test value. The
package docs live under `docs/` beside this file.
-/
