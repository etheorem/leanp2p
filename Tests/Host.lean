import Std.Data.HashMap
import Tests.Support
import Conc
import Streams
import Multiformats
import Libp2p.Host

/-!
# Host suite (unit W5.6)

The checks of `packages/libp2p/host/docs/PLAN.md`.

Unit 1a: the dedup rule, the session table's liveness, the handler
table, the peerstore, and the `Host.Error` lines. Every check runs the
pure update functions, by value or under an `OnceRef`, with no
connection in the loop. The session handle of a table entry is a `Nat`
here, since the rule never reads it.

Unit 1b runs hosts over the sim transport, with the real
`Noise.securityProtocol` and `Mux.yamux` values (PRINCIPLES 1.4). Every
host derives its peer id through `libp2p/identity`, and the upgrade runs
through `libp2p/negotiate`, so the legs wait for W5.3, W5.4, and W5.5
to merge. Until then the suite names each leg as a skip.
-/

set_option autoImplicit false

namespace Tests

open Conc Multiformats Libp2p.Identity Libp2p.Host.Mock.Core Libp2p.Host

/-! ## Helpers -/

/-- A multiaddr from its text form. -/
private def ma (s : String) : IO Multiaddr := do
  match Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- The smaller and the larger of two test peers: the inlined ids of
the one-byte keys `1` and `2`. Their binary forms are `[0x00, 0x01, 1]`
and `[0x00, 0x01, 2]`, so `small` orders first. The size bound
`1 ≤ 42` holds by evaluation. -/
private def small : PeerId := PeerId.inline (ByteArray.mk #[1]) (by decide)
private def large : PeerId := PeerId.inline (ByteArray.mk #[2]) (by decide)

/-- A live table entry. -/
private def entry (id : Nat) (role : Role) (bornMs : Nat) : Entry Nat :=
  { id, role, bornMs, live := true, session := id }

/-- The session number of the entry of `peer`, when it has one. -/
private def holder (t : SessionTable Nat) (peer : PeerId) : Option Nat :=
  (t.get? peer).map (·.id)

/-- True when the decision committed the candidate and displaced the
session `id` (`none`: displaced nothing). -/
private def committedOver (d : Decision Nat) (id : Option Nat) : Bool :=
  match d with
  | .commit displaced => displaced.map (·.id) == id
  | .keep _ => false

/-- True when the decision kept the standing session `id`. -/
private def keptId (d : Decision Nat) (id : Nat) : Bool :=
  match d with
  | .keep s => s.id == id
  | .commit _ => false

/-! ## Dedup -/

/-- The rule of the package ARCHITECTURE, contract 2, run by value. -/
private def dedupChecks (r : Runner) : IO Unit := do
  r.check "the binary order puts the smaller test peer first" (comparePeers small large == .lt)

  -- An absent slot, and a dead standing session, take the candidate.
  let (d, t) := dedup small large (entry 1 .initiator 0) {}
  r.check "an empty slot takes the candidate" (committedOver d none && holder t large == some 1)
  let dead : SessionTable Nat := ({} : SessionTable Nat).insert large { entry 1 .initiator 0 with live := false }
  let (d, t) := dedup small large (entry 2 .initiator 10) dead
  r.check "a dead standing session makes room" (committedOver d none && holder t large == some 2)

  -- A race inside the window: the connection the larger id dialed
  -- loses. Each case runs on the side that holds the larger id and on
  -- the side that holds the smaller one, and the standing session
  -- runs first in one direction and then in the other.
  let born := 1000
  let inWindow := born + simulWindowMs - 1
  -- We hold the smaller id. The peer (larger) dialed the standing
  -- session, so it loses to our new dial.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .responder born)
  let (d, t) := dedup small large (entry 2 .initiator inWindow) standing
  r.check "smaller side: our dial beats the larger peer's dial" (committedOver d (some 1) && holder t large == some 2)
  -- We hold the smaller id, and we dialed the standing session. The
  -- larger peer's dial arrives and loses.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .initiator born)
  let (d, t) := dedup small large (entry 2 .responder inWindow) standing
  r.check "smaller side: the larger peer's dial loses to ours" (keptId d 1 && holder t large == some 1)
  -- We hold the larger id, and we dialed the standing session. The
  -- smaller peer's dial arrives and wins.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert small (entry 1 .initiator born)
  let (d, t) := dedup large small (entry 2 .responder inWindow) standing
  r.check "larger side: the smaller peer's dial beats ours" (committedOver d (some 1) && holder t small == some 2)
  -- We hold the larger id. The smaller peer dialed the standing
  -- session, and our own dial loses to it.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert small (entry 1 .responder born)
  let (d, t) := dedup large small (entry 2 .initiator inWindow) standing
  r.check "larger side: our dial loses to the smaller peer's" (keptId d 1 && holder t small == some 1)

  -- The window edge: a candidate born `simulWindowMs` after the
  -- standing session is outside it, and the standing session stays,
  -- even when the race rule would have dropped it.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .responder born)
  let (d, _) := dedup small large (entry 2 .initiator (born + simulWindowMs)) standing
  r.check "outside the window the live standing session stays" (keptId d 1)
  -- The same direction is no race: a second dial of ours keeps the
  -- first session, inside the window too.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .initiator born)
  let (d, t) := dedup small large (entry 2 .initiator inWindow) standing
  r.check "a second dial in the same direction keeps the first" (keptId d 1 && holder t large == some 1)

  -- Both sides at once. Peer `small` dialed connection A, and peer
  -- `large` dialed connection B. Each side committed one first; the
  -- other then arrives as the candidate. Both keep A, the connection
  -- that the smaller id dialed.
  for aFirstOnSmall in [true, false] do
    for aFirstOnLarge in [true, false] do
      -- On `small`, A is ours (`.initiator`), and B is the peer's.
      let (firstS, secondS) :=
        if aFirstOnSmall then (entry 0 .initiator born, entry 1 .responder inWindow)
        else (entry 1 .responder born, entry 0 .initiator inWindow)
      let (_, ts) := dedup small large firstS {}
      let (_, ts) := dedup small large secondS ts
      -- On `large`, A is the peer's (`.responder`), and B is ours.
      let (firstL, secondL) :=
        if aFirstOnLarge then (entry 0 .responder born, entry 1 .initiator inWindow)
        else (entry 1 .initiator born, entry 0 .responder inWindow)
      let (_, tl) := dedup large small firstL {}
      let (_, tl) := dedup large small secondL tl
      r.check s!"both sides keep the smaller id's dial (A first on small: {aFirstOnSmall}, on large: {aFirstOnLarge})"
        (holder ts large == some 0 && holder tl small == some 0)

/-- Many decisions over one peer under one cell: each runs as its own
task, through `OnceRef.updateGet`, and the table ends with exactly the
survivor the decisions name (PRINCIPLES 3.3). -/
private def concurrentDedupChecks (r : Runner) : Async Unit := do
  -- Sixteen dials of ours to one peer, all in the same direction: one
  -- commits, the rest keep it, and no update is lost.
  let cell : OnceRef (SessionTable Nat) ← OnceRef.new {}
  let answers : OnceRef (List (Decision Nat)) ← OnceRef.new []
  let ts ← TaskSet.new
  for i in [0:16] do
    ts.spawn do
      let d ← (cell.updateGet (dedup small large (entry i .initiator 0)) : BaseIO (Decision Nat))
      answers.update (d :: ·)
  ts.joinAll
  let ds ← (answers.get : BaseIO (List (Decision Nat)))
  let t ← (cell.get : BaseIO (SessionTable Nat))
  let winners := ds.filter (·.committed)
  r.check "sixteen same-direction dials: one commits" (winners.length == 1)
  r.check "sixteen same-direction dials: the rest keep the winner"
    (ds.all fun d => match d, holder t large with
      | .keep s, some w => s.id == w
      | .commit none, _ => true
      | _, _ => false)

  -- Two opposite dials inside the window, in either order: the table
  -- ends with the smaller id's dial, and the decisions agree with it.
  for _ in [0:8] do
    let cell : OnceRef (SessionTable Nat) ← OnceRef.new {}
    let answers : OnceRef (List (Decision Nat)) ← OnceRef.new []
    let ts ← TaskSet.new
    -- On `small`, our dial is the smaller id's dial.
    for (i, role) in [(0, Role.initiator), (1, Role.responder)] do
      ts.spawn do
        let d ← (cell.updateGet (dedup small large (entry i role 0)) : BaseIO (Decision Nat))
        answers.update (d :: ·)
    ts.joinAll
    let t ← (cell.get : BaseIO (SessionTable Nat))
    let ds ← (answers.get : BaseIO (List (Decision Nat)))
    r.check "two opposite dials: the smaller id's dial survives" (holder t large == some 0)
    -- The peer's dial (1) is displaced when it ran first, and kept out
    -- when it ran second; our dial (0) never loses.
    r.check "two opposite dials: the decisions name the survivor"
      (ds.all fun d => match d with
        | .keep s => s.id == 0
        | .commit (some s) => s.id == 1
        | .commit none => true)

/-- Liveness is a table field (contract 3): a session that exits marks
its entry dead through the cell, and the next decision reads it. -/
private def livenessChecks (r : Runner) : Async Unit := do
  let cell : OnceRef (SessionTable Nat) ← OnceRef.new {}
  discard <| (cell.updateGet (dedup small large (entry 1 .initiator 0)) : BaseIO (Decision Nat))
  -- The session loop runs as a task and marks its exit on the way out.
  let ts ← TaskSet.new
  ts.spawn do cell.update (SessionTable.markDead large 1)
  ts.joinAll
  let t ← (cell.get : BaseIO (SessionTable Nat))
  r.check "an exited session reads as dead" ((t.get? large).any (!·.live) && (t.live? large).isNone)
  -- A dial outside any race takes the slot of the dead session.
  let d ← (cell.updateGet (dedup small large (entry 2 .initiator 5)) : BaseIO (Decision Nat))
  r.check "the next decision replaces the dead session" (committedOver d none)
  -- The late exit of the replaced session leaves its successor live.
  cell.update (SessionTable.markDead large 1)
  let t ← (cell.get : BaseIO (SessionTable Nat))
  r.check "a stale exit leaves the successor live" ((t.live? large).any (·.id == 2))
  r.check "the live entries list the successor"
    ((SessionTable.liveEntries t).map (·.2.id) == [2])

/-! ## The handler table -/

/-- A handler that half-closes its stream. -/
private def closer (id : ProtocolId) : StreamHandler where
  id := id
  handle := fun _ s => s.close

private def handlerChecks (r : Runner) : Async Unit := do
  let ping : ProtocolId := ⟨"/ipfs/ping/1.0.0"⟩
  let ident : ProtocolId := ⟨"/ipfs/id/1.0.0"⟩
  -- A handler set under the cell is visible to the next read.
  let cell : OnceRef Handlers ← OnceRef.new {}
  let ts ← TaskSet.new
  for h in [closer ping, closer ident] do
    ts.spawn do cell.update (Handlers.set h)
  ts.joinAll
  let t ← (cell.get : BaseIO Handlers)
  r.check "a set handler is found by its id" ((t.find? ping).any (·.id == ping))
  r.check "an unknown id finds no handler" (t.find? ⟨"/ipfs/ping/2.0.0"⟩).isNone
  r.check "the table lists its ids in text order" (Handlers.ids t == [ident, ping])
  let t := Handlers.set (closer ping) t
  r.check "a second set under one id replaces the first" (Handlers.ids t == [ident, ping])

/-! ## The peerstore -/

private def peerstoreChecks (r : Runner) : Async Unit := do
  let a1 ← ma "/ip4/10.0.0.1/tcp/4001"
  let a2 ← ma "/ip6/::1/tcp/4002"
  let a3 ← ma "/memory/3"
  -- Addresses round-trip, in the order they arrived.
  let s := Peerstore.addAddrs large [a1, a2] {}
  r.check "the peerstore returns the added addresses" (Peerstore.addrsOf s large == [a1, a2])
  r.check "an unknown peer has no addresses" (Peerstore.addrsOf s small).isEmpty
  -- A redial's re-add of the same address grows nothing.
  let s' := Peerstore.addAddrs large [a2, a1] s
  r.check "a re-add leaves the set unchanged" (Peerstore.addrsOf s' large == [a1, a2])
  let s' := Peerstore.addAddrs large [a3, a3] s'
  r.check "a new address joins once" (Peerstore.addrsOf s' large == [a1, a2, a3])

  -- N tasks add to one store under the cell: every address lands, and
  -- none twice (the base/conc milestone shape).
  let cell : OnceRef Peerstore ← OnceRef.new {}
  let addrs ← (List.range 32).mapM fun i => ma s!"/ip4/10.0.0.{i}/tcp/4001"
  let ts ← TaskSet.new
  for a in addrs do
    -- Each address goes in twice, from two tasks.
    for _ in [0:2] do
      ts.spawn do cell.update (Peerstore.addAddrs large [a])
  ts.joinAll
  let got := Peerstore.addrsOf (← (cell.get : BaseIO Peerstore)) large
  r.check "concurrent adds keep every address" (addrs.all got.contains)
  r.check "concurrent adds keep each address once" (got.length == addrs.length)

/-! ## `Host.Error` -/

private def errorChecks (r : Runner) : IO Unit := do
  let a ← ma "/memory/7"
  let arms : List (Libp2p.Host.Error × String) :=
    [(.upgrade (.timeout "30000 ms"), "upgrade failed: timeout: 30000 ms"),
     (.session (.protocol "bad frame"), "session failed: protocol error: bad frame"),
     (.stream (.closed "reset"), "stream failed: closed: reset"),
     (.gated .secured, "refused by policy at the secured checkpoint"),
     (.noAddresses large, s!"no address for peer {large}"),
     (.noTransport a, "no transport handles /memory/7"),
     (.unreachable a, "nobody listens at /memory/7"),
     (.dialSelf, "a dial to our own peer id"),
     (.closing, "the host is closing")]
  for (e, line) in arms do
    r.check s!"Host.Error renders {line}" (toString e == line)

/-! ## Unit 1b -/

/-- The unit 1b legs of the plan. Each one needs a host, and a host
derives its peer id through `libp2p/identity` and upgrades through
`libp2p/negotiate` (module doc). -/
private def swarmLegs : List String :=
  ["the upgrade pipeline in both directions, with the identity check",
   "the host's own answers: dial to self, no address, no transport, unknown protocol, failing handler, after close",
   "the policy doubles: a denying gater refuses a dial and an inbound connection",
   "the silent peer at the deadline, and close reaching a parked upgrade",
   "the shutdown stages of §5.5 in order",
   "the leftover hand-over on a served stream"]

def Host.run (r : Runner) : IO Unit := do
  r.section "host" "(packages/libp2p/host/docs/PLAN.md, test milestones, units 1a and 1b)"
  dedupChecks r
  (concurrentDedupChecks r).run
  (livenessChecks r).run
  (handlerChecks r).run
  (peerstoreChecks r).run
  errorChecks r
  for leg in swarmLegs do
    r.skip s!"host: {leg}" "needs W5.3, W5.4, and W5.5 merged"

end Tests
