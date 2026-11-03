import Libp2p.Core.ProtocolId
import Libp2p.Core.Error
import Libp2p.Core.Security
import Libp2p.Core.Mux
import Libp2p.Core.Handler
import Libp2p.Core.Policy

/-!
# Libp2p.Core

Shared libp2p types and interfaces (ARCHITECTURE §4.9).
Import this root to use the public API. Protocol implementations live
in the security, mux, negotiate, host, and protocols packages.

Temporary dependency mocks and their integration steps are documented
in `docs/ARCHITECTURE.md`.
-/
