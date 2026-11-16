import Tests.Support
import Tests.HostPair

/-!
# Leak scenarios (#102)

Small scenarios for a LeakSanitizer build of the suite. Each runs alone
(`LEANP2P_SUITE=leak-clock`, `leak-pair`, `leak-handler`,
`leak-late-handler`), so a leak report names the smallest piece that
keeps its objects alive. Each one
builds, uses, and closes its objects, and keeps no reference past its
end. The normal suite does not run them.

- `leak-clock` gives the floor: a test clock alone. The records it
  shows are the runtime's one-time objects.
- `leak-pair` is a host pair that dials and closes. It shows the floor
  of a pair: one-time objects of the stack it starts.
- `leak-handler` adds a handler that holds its own host, as
  `Identify.pushHandler p.server` does. Without the handler table's
  release at `Host.close`, the host stays allocated with its sessions,
  and the report shows more than `leak-pair`.
- `leak-late-handler` sets that handler again after the close. The
  closed table takes nothing, so the report matches `leak-pair`.
-/

set_option autoImplicit false

namespace Tests.Leak

open Conc
open Tests.HostPair (hostPair)

/-- A test clock, made and closed. -/
def clockOnly (r : Runner) : IO Unit := Async.run do
  r.section "leak: clock" "#102"
  let tc ← (TestClock.new : BaseIO TestClock)
  (tc.close : BaseIO Unit)
  r.check "leak: the clock closes" true

/-- A host pair that dials, then closes. -/
def pairOnly (r : Runner) : IO Unit := Async.run do
  r.section "leak: pair" "#102"
  let p ← hostPair
  r.check "leak: the pair closes" (← p.close).isNone

/-- A host pair whose server handler captures the server host, as
`Identify.pushHandler p.server` does: the host's handler table holds a
closure that holds the host. -/
def pairSelfHandler (r : Runner) : IO Unit := Async.run do
  r.section "leak: handler that holds its host" "#102"
  let p ← hostPair
  let server := p.server
  let selfRef : Libp2p.Core.StreamHandler :=
    { id := ⟨"/leak/2"⟩
      handle := fun _ s => ExceptT.mk do
        -- The read of the host keeps it in the closure.
        if ← (server.isClosing : BaseIO Bool) then s.reset else s.close
        return .ok () }
  server.setHandler selfRef
  r.check "leak: the pair closes" (← p.close).isNone

/-- `leak-handler`, then the same handler set again after the close:
`close` took the table, so the call stores nothing, and the host is
freed as in `leak-handler`. -/
def lateSelfHandler (r : Runner) : IO Unit := Async.run do
  r.section "leak: handler set after the close" "#102"
  let p ← hostPair
  let server := p.server
  let selfRef : Libp2p.Core.StreamHandler :=
    { id := ⟨"/leak/3"⟩
      handle := fun _ s => ExceptT.mk do
        if ← (server.isClosing : BaseIO Bool) then s.reset else s.close
        return .ok () }
  server.setHandler selfRef
  r.check "leak: the pair closes" (← p.close).isNone
  (server.setHandler selfRef : BaseIO Unit)

end Tests.Leak
