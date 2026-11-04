import Tests.Support
import Libp2p.Mux

/-!
# Mux suite (unit W5.4)

The constant checks this slice can run: the three protocol ids and
the named mplex cap (`packages/libp2p/mux/docs/PLAN.md`, the id
milestone, and `packages/libp2p/mux/docs/ARCHITECTURE.md`, the
constants module).
-/

set_option autoImplicit false

namespace Tests

open Libp2p.Mux

def Mux.run (r : Runner) : IO Unit := do
  r.section "mux constants" "packages/libp2p/mux/docs/ARCHITECTURE.md"
  r.check "yamuxId.toString is /yamux/1.0.0"
    (yamuxId.toString == "/yamux/1.0.0")
  r.check "mplexId.toString is /mplex/6.7.0"
    (mplexId.toString == "/mplex/6.7.0")
  r.check "testId.toString is /leanp2p/test-mux/1.0.0"
    (testId.toString == "/leanp2p/test-mux/1.0.0")
  r.check "mplexMessageCap is 1 MiB"
    (mplexMessageCap == 1024 * 1024)
  r.check "the three protocol ids are pairwise distinct"
    (yamuxId.toString != mplexId.toString
      && yamuxId.toString != testId.toString
      && mplexId.toString != testId.toString)

end Tests
