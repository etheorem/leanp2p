import Libp2p.Host.Constants
import Libp2p.Host.Error
import Libp2p.Host.Registry
import Libp2p.Host.Dedup
import Libp2p.Host.Peerstore
import Libp2p.Host.Policy
import Libp2p.Host.Gate
import Libp2p.Host.Swarm
import Libp2p.Host.Shutdown

/-!
# Libp2p.Host

The host subpackage: the upgrade pipeline, dedup, and the peerstore
(ARCHITECTURE §4.9). The package docs live under `docs/` beside this
file. The root re-exports each public submodule.
-/
