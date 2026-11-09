import Libp2p.Negotiate.Legacy.Constants
import Libp2p.Negotiate.Legacy.Message
import Libp2p.Negotiate.Legacy.Step
import Libp2p.Negotiate.Legacy.Upgrade

/-!
# The legacy negotiate surface

The host of this branch still runs the pre-seam negotiate API: `upgradeWith` with the
checkpoint hook and `negotiateStream` per muxed stream. The reviewed tip carries the seam
versions of the negotiate package (issue #70 tracks the host swap), so this module keeps the
legacy entry points beside them, under their own namespace. Host files import this module
instead of `Libp2p.Negotiate`.
-/
