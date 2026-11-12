import Libp2p.Negotiate.Constants
import Libp2p.Negotiate.Message
import Libp2p.Negotiate.Step
import Libp2p.Negotiate.Upgrade
import Libp2p.Negotiate.Secured

/-!
# Libp2p.Negotiate

The negotiate subpackage: multistream-select 1.0.0 and the upgrader
(ARCHITECTURE §4.9). One import line per public submodule. The seam
types come from `Libp2p.Core`, and the identity field types name
`Libp2p.Identity`.
-/
