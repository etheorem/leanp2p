import Libp2p.Protocols.Constants
import Libp2p.Protocols.Identity
import Libp2p.Protocols.Identify
import Libp2p.Protocols.Ping
import Libp2p.Protocols.ReqResp.Crc32c
import Libp2p.Protocols.ReqResp.SnappyFrame
import Libp2p.Protocols.ReqResp.Payload
import Libp2p.Protocols.ReqResp.Core
import Libp2p.Protocols.ReqResp.Limiter
import Libp2p.Protocols.ReqResp.Exchange

/-!
# Libp2p.Protocols

The protocols subpackage: identify and ping first, then req/resp, and
gossipsub last (ARCHITECTURE §4.9). The package docs live under `docs/`
beside this file.
-/
