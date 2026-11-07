import Libp2p.Mux.Constants
import Libp2p.Mux.Mock.Core
import Libp2p.Mux.Test.Session

/-!
# The public test muxer

`Mux.test` is the `Muxer` for the private test session. `open` passes
the role, the connection, and the negotiation leftover to
`Session.start`. `ExceptT.lift` returns that session on the seam.
The lift adds no error arm.
-/

set_option autoImplicit false

namespace Libp2p.Mux

open Mock.Core

/-- The independent test muxer. `id` is `testId`. `open` starts the
private session. The leftover bytes are the reader's first input. -/
def test : Muxer where
  id := testId
  «open» := fun role connection leftover =>
    ExceptT.lift (Test.Session.start role connection leftover)

end Libp2p.Mux
