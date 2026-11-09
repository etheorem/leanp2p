import Conc
import Libp2p.Core.ProtocolId
import Libp2p.Protocols.Constants

/-!
# Req/resp: the concurrent-request limit

"The requester MUST NOT make more than `MAX_CONCURRENT_REQUESTS`
concurrent requests with the same protocol ID" (phase0
`p2p-interface.md`, "Requesting side"; the value is 2, "Configs"). The
limit holds toward one peer, so the requester keeps one `Limiter` per
peer, and the owner of the peer's connection keeps it.

The rule is a pure table update, `Table.take` and `Table.give`, and the
shell applies each in one `OnceRef.updateGet` (ARCHITECTURE §4.1, rule
3), so two requests cannot both see a free slot that only one of them
gets. A request that finds no free slot is refused at once: the spec
forbids the request, and a wait would park the caller on another
request's deadline.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp

open Libp2p.Protocols
open Libp2p.Core (ProtocolId)

/-- The open requests per protocol id. An id with no entry has none. -/
abbrev Table := List (ProtocolId × Nat)

/-- The open requests of `id`. -/
def Table.count (t : Table) (id : ProtocolId) : Nat :=
  ((t.find? (·.1 == id)).map (·.2)).getD 0

/-- The table with the count of `id` set to `n`. -/
def Table.set (t : Table) (id : ProtocolId) (n : Nat) : Table :=
  (id, n) :: t.filter (·.1 != id)

/-- Take a slot for `id` when one is free: the answer, and the table. -/
def Table.take (t : Table) (id : ProtocolId) : Bool × Table :=
  if t.count id < Constants.maxConcurrentRequests then (true, t.set id (t.count id + 1))
  else (false, t)

/-- Give back the slot of `id`. -/
def Table.give (t : Table) (id : ProtocolId) : Table :=
  t.set id (t.count id - 1)

/-- The count of an id just set is the value set. -/
theorem Table.countSet (t : Table) (id : ProtocolId) (n : Nat) : (t.set id n).count id = n := by
  simp [Table.set, Table.count]

/-- A take never lifts a count past the limit, whatever the table held
at or below it. -/
theorem Table.takeBounded (t : Table) (id : ProtocolId)
    (h : t.count id ≤ Constants.maxConcurrentRequests) :
    (t.take id).2.count id ≤ Constants.maxConcurrentRequests := by
  unfold Table.take
  split
  · rw [Table.countSet]; omega
  · exact h

/-- A take that answers `true` added exactly one request. -/
theorem Table.takeTrue (t : Table) (id : ProtocolId) (h : (t.take id).1 = true) :
    (t.take id).2.count id = t.count id + 1 := by
  unfold Table.take at *
  split at h
  · next hlt => simp only [hlt, ↓reduceIte, Table.countSet]
  · simp at h

/-- The open requests toward one peer. -/
structure Limiter where
  /-- The table, changed only in one `updateGet` or `update`. -/
  table : Conc.OnceRef Table

/-- A limiter with no open request. -/
def Limiter.new : BaseIO Limiter := do
  return ⟨← Conc.OnceRef.new []⟩

/-- Take a slot for `id`; `false` when `MAX_CONCURRENT_REQUESTS`
requests with `id` are open. -/
def Limiter.take (l : Limiter) (id : ProtocolId) : BaseIO Bool :=
  l.table.updateGet (·.take id)

/-- Give back a slot that `take` gave. -/
def Limiter.give (l : Limiter) (id : ProtocolId) : BaseIO Unit :=
  l.table.update (·.give id)

end Libp2p.Protocols.ReqResp
