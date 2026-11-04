import Std
import Conc
import Libp2p.Protocols.Mock.Identity

/-!
# Host peerstore mock

`Libp2p.Host` (issue #19) is not merged. This mock declares the
peerstore surface that the identify push handler updates, from
`packages/libp2p/host/docs/ARCHITECTURE.md`: `addAddrs`, deduplicated
at add, and `addrsOf`. The host doc freezes the names and the dedup
rule, and it leaves the signatures open. This mock fixes minimal
signatures. The real host package replaces this module at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Host

open Libp2p.Protocols.Mock.Identity

/-- The peerstore seam the push handler updates: addresses by peer,
deduplicated at add. -/
structure Peerstore where
  /-- Store the addresses of one peer, deduplicated at add. -/
  addAddrs : PeerId → List (List Nat) → IO Unit
  /-- The stored addresses of one peer. -/
  addrsOf : PeerId → IO (List (List Nat))

/-- The executable in-memory double. Each call makes a fresh table:
bind the action once, and pass the resulting value to both the handler
and `addrsOf`. A second add of the same addresses grows nothing. The
table changes through `OnceRef.update`, one atomic step per add
(ARCHITECTURE §4.1, rule 3). -/
opaque inMemory : IO Peerstore := do
  let table ← Conc.OnceRef.new ([] : List (PeerId × List (List Nat)))
  let addAddrs : PeerId → List (List Nat) → IO Unit := fun p addrs =>
    table.update fun cur =>
      let old := (cur.find? (fun e => e.1 == p)).map (·.2) |>.getD []
      let merged := (old ++ addrs).eraseDups
      (p, merged) :: cur.filter (fun e => !(e.1 == p))
  let addrsOf : PeerId → IO (List (List Nat)) := fun p => do
    let cur ← table.get
    return (cur.find? (fun e => e.1 == p)).map (·.2) |>.getD []
  return { addAddrs, addrsOf }

end Libp2p.Protocols.Mock.Host
