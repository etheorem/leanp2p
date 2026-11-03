import Libp2p.Protocols.Constants
import Libp2p.Protocols.Identify
import Libp2p.Protocols.Ping

/-!
# Libp2p.Protocols

The protocols subpackage: identify and ping first, then req/resp and
gossipsub (ARCHITECTURE §4.9). Sub-unit 1a of W5.7 lands the pure
identify and ping code. The IO handlers and clients are sub-unit 1b.
The package docs live under `docs/` beside this file.
-/
