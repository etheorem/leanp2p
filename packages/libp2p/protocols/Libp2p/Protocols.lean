import Libp2p.Protocols.Constants
import Libp2p.Protocols.Gossipsub.Types
import Libp2p.Protocols.Gossipsub.Rpc
import Libp2p.Protocols.Gossipsub.Score
import Libp2p.Protocols.Gossipsub.Cache
import Libp2p.Protocols.Gossipsub.Sign
import Libp2p.Protocols.Gossipsub.Core

/-!
# Libp2p.Protocols

The protocols subpackage (ARCHITECTURE §4.9). This pull request carries
the gossipsub modules. Identify, ping and req/resp arrive with their own
units. The package docs live under `docs/` beside this file.
-/
