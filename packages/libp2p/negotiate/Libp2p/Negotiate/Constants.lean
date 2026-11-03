import Libp2p.Negotiate.Mock.Core

/-!
# The constants of the negotiation

One home per fact (root §3.8). The multistream protocol id and the
1 KiB message cap live only here. At W5.2 integration the `Mock.Core`
import swaps to `Libp2p.Core`, and the literal stays.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate

/-- The multistream 1.0.0 protocol id. The only string literal of the
package (root §3.4). -/
def protocolId : Mock.Core.ProtocolId := ⟨"/multistream/1.0.0"⟩

/-- The 1 KiB multistream cap (root §5.1, contract 1 of the package
docs). -/
def maxMsg : Nat := 1024

end Libp2p.Negotiate
