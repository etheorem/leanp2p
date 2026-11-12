import Libp2p.Security.Constants
import Libp2p.Security.Handshake
import Libp2p.Security.Payload
import Libp2p.Security.Transport
import Libp2p.Security.Noise
import Libp2p.Security.Tls.Constants
import Libp2p.Security.Tls.SignedKey
import Libp2p.Security.Tls.Certificate
import Libp2p.Security.Tls.Protocol

/-!
# Libp2p.Security

The security subpackage: Noise XX and the libp2p TLS handshake as
`SecurityProtocol` values (ARCHITECTURE §4.9). Unit 1a of W5.3 holds
the Noise constants, the XX core, and the payload check; unit 1b adds
the Noise transport and the seam values. W5.11 adds `Tls/`: the
`SignedKey` codec, the certificate checks, and `/tls/1.0.0` over the
engine of `net/tls`. The package docs live under `docs/` beside this
file.
-/
