import Libp2p.Core.ProtocolId

/-!
# The constants of `libp2p/mux`

Each fact has one home (ARCHITECTURE §3.8). This module holds the
three protocol ids and the mplex length cap. The production
definitions of the ids live only here (§3.4).

`ProtocolId` comes from `Libp2p.Core.ProtocolId`. This module imports
that file alone, so the constants do not import the session seam.
-/

set_option autoImplicit false

namespace Libp2p.Mux

open Libp2p.Core

/-- The yamux protocol id. Peers negotiate `/yamux/1.0.0` on the wire. -/
def yamuxId : ProtocolId := { toString := "/yamux/1.0.0" }

/-- The mplex protocol id. Peers negotiate `/mplex/6.7.0` on the wire. -/
def mplexId : ProtocolId := { toString := "/mplex/6.7.0" }

/-- The repository-local protocol id for test suites:
`/leanp2p/test-mux/1.0.0`. -/
def testId : ProtocolId := { toString := "/leanp2p/test-mux/1.0.0" }

/-- The mplex declared-length cap: 1 MiB, spelled `1024 * 1024`.
The future P2 mplex implementation checks a declared length against
this cap before allocation. This module names the cap. -/
def mplexMessageCap : Nat := 1024 * 1024

end Libp2p.Mux
