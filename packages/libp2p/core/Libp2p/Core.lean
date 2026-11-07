import Libp2p.Core.ProtocolId
import Libp2p.Core.Error
import Libp2p.Core.Role
import Libp2p.Core.Security
import Libp2p.Core.Mux
import Libp2p.Core.Handler
import Libp2p.Core.Policy

/-!
# Libp2p.Core

The core subpackage: the libp2p-wide types and the seams (ARCHITECTURE
§4.9). The root module re-exports one public submodule per line, so an
implementation or the upgrader imports one name. The package docs live
under `docs/` beside this file.
-/
