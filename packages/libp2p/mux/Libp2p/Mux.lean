import Libp2p.Mux.Constants
import Libp2p.Mux.Yamux
import Libp2p.Mux.Test
import Libp2p.Mux.Mplex

/-!
# Libp2p.Mux

The mux subpackage: the `Muxer` values over the muxer sessions
(ARCHITECTURE §4.9). This root imports each public submodule.
`Constants.lean` holds the ids. `Yamux.lean` holds `Mux.yamux`.
`Test.lean` holds `Mux.test`. `Mplex.lean` holds `Mux.mplex`. The
package docs live under `docs/` beside this file.
-/
