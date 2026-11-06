import Yamux.Constants
import Yamux.Sets
import Yamux.Header
import Yamux.Core
import Yamux.Invariants
import Yamux.Loop
import Yamux.Session

/-!
# Yamux

The yamux session, the interop muxer (ARCHITECTURE §4.8): the 12-byte
header codec with its proved round trip, the session as a pure `step`
with its invariant theorems, and the loop that serves `Stream` values
over a `Connection` of `net/streams`. The package docs live under
`docs/` beside this file.
-/
