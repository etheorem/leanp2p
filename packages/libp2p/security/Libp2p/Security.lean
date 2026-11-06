import Libp2p.Security.Constants
import Libp2p.Security.Handshake
import Libp2p.Security.Payload
import Libp2p.Security.Transport
import Libp2p.Security.Noise

/-!
# Libp2p.Security

The security subpackage: Noise XX as a `SecurityProtocol` value
(ARCHITECTURE §4.9). Unit 1a of W5.3 holds the constants, the XX core,
and the payload check; unit 1b adds the transport and the seam values.
The package docs live under `docs/` beside this file.
-/
