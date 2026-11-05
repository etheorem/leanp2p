import Libp2p.Host.Mock.Identity
import Libp2p.Host.Mock.Core
import Libp2p.Host.Constants
import Libp2p.Host.Registry

/-!
# The dedup rule

The host keeps one session per peer (ARCHITECTURE §4.9). When a new
session to a peer finishes its upgrade, one pure function over the
session table decides which session the peer keeps, and the host
applies it with `OnceRef.updateGet`. The table holds the liveness of
each session as data (§3.8), so no IO read runs between a probe and a
commit, and no other update can change the entry under the decision
(the package ARCHITECTURE, contracts 2 and 3).

## The rule

The new session is the candidate. The entry already in the table, if
any, is the standing session.

1. No standing session, or a dead one: the candidate takes the slot.
2. A live standing session and a candidate that run in opposite
   directions, with the standing session born less than
   `simulWindowMs` before the candidate: the two dials raced. The
   connection that the larger peer id dialed loses (§4.9), and the
   other one keeps the slot.
3. Any other live standing session keeps the slot, and the candidate
   loses: outside the window, or in the same direction.

Both peers must pick the same survivor in case 2, and each runs the
rule on its own. Our side dialed the connection where our role is
`.initiator`, so the loser is the connection whose initiator holds the
larger id. Both sides compare the same two ids, so they agree.

## The order on peer ids

"Larger" is the order of the binary form (`PeerId.toBytes`, the
multihash bytes), byte by byte. Both peers hold the same bytes for
each id. The derived `Ord` of `PeerId` also compares the text form
that one side parsed the id in, and the two sides can hold different
forms, so the rule does not use it.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Libp2p.Host.Mock.Identity Libp2p.Host.Mock.Core

/-- The order of two peer ids by their binary form, byte by byte
(module doc, "The order on peer ids"). -/
def comparePeers (a b : PeerId) : Ordering :=
  compare a.toBytes.toList b.toBytes.toList

/-- The answer of the dedup rule for one candidate. -/
inductive Decision (α : Type) where
  /-- The candidate took the slot. `displaced` is the live session it
  replaced, which the caller closes; `none` when the slot was empty or
  held a dead session. -/
  | commit (displaced : Option (Entry α))
  /-- The standing session keeps the slot, and the caller closes the
  candidate. The caller serves the peer through `standing`. -/
  | keep (standing : Entry α)

namespace Decision

variable {α : Type}

/-- True when the candidate took the slot. -/
def committed : Decision α → Bool
  | .commit _ => true
  | .keep _ => false

end Decision

/-- The role of the connection that loses a race between two peers:
the one whose initiator holds the larger id. Our side initiated the
connection where our role is `.initiator`. -/
def raceLoser (localPeer remotePeer : PeerId) : Role :=
  if comparePeers localPeer remotePeer = .gt then .initiator else .responder

/-- True when the standing session and a candidate born at `nowMs`
raced: they run in opposite directions, and the standing session was
born less than `simulWindowMs` before. -/
def raced {α : Type} (standing : Entry α) (candidateRole : Role) (nowMs : Nat) : Bool :=
  standing.role != candidateRole && nowMs < standing.bornMs + simulWindowMs

/-- The dedup rule (module doc, "The rule"): decide whether `cand`
takes the slot of `remotePeer`, and the table after the decision. The
candidate's `bornMs` is the time of the decision. -/
def dedup {α : Type} (localPeer remotePeer : PeerId) (cand : Entry α)
    (t : SessionTable α) : Decision α × SessionTable α :=
  let commit (displaced : Option (Entry α)) := (.commit displaced, t.insert remotePeer cand)
  match t.get? remotePeer with
  | none => commit none
  | some standing =>
    if !standing.live then commit none
    else if raced standing cand.role cand.bornMs then
      if cand.role = raceLoser localPeer remotePeer then (.keep standing, t)
      else commit (some standing)
    else (.keep standing, t)

/-! ## Theorems

The rule is a pure function, so its properties are theorems (§3.3,
§6). `HashMap` lookups appear as `t[r]?`, the form `simp` normalizes
`get?` to. -/

/-- Both peers pick the same survivor of a race. Peer `a` dialed one
connection, so `a` holds it as `.initiator` and `b` holds it as
`.responder`. The roles the two sides drop differ, so the one
connection that `a` drops as its initiator is the one `b` drops as its
responder, and the other way round. The ids differ: a dial to our own
id never reaches dedup (`Error.dialSelf`). -/
theorem raceLoserAgree (a b : PeerId) (h : comparePeers a b ≠ .eq) :
    raceLoser a b ≠ raceLoser b a := by
  unfold raceLoser comparePeers at *
  -- The list order is oriented: swapping the arguments swaps the answer.
  have hs : compare a.toBytes.toList b.toBytes.toList =
      (compare b.toBytes.toList a.toBytes.toList).swap := Std.OrientedOrd.eq_swap
  cases hc : compare b.toBytes.toList a.toBytes.toList <;> simp_all [Ordering.swap]

/-- An empty slot takes the candidate (rule 1). -/
theorem dedupEmpty {α : Type} (l r : PeerId) (c : Entry α) (t : SessionTable α)
    (h : t[r]? = none) : dedup l r c t = (.commit none, t.insert r c) := by
  simp [dedup, h]

/-- A dead standing session always makes room (rule 1), and nothing is
displaced. -/
theorem dedupDead {α : Type} (l r : PeerId) (c s : Entry α) (t : SessionTable α)
    (h : t[r]? = some s) (hd : s.live = false) :
    dedup l r c t = (.commit none, t.insert r c) := by
  simp [dedup, h, hd]

/-- A decision that keeps the standing session leaves the table as it
was, so a losing candidate changes no state. -/
theorem dedupKeepTable {α : Type} (l r : PeerId) (c s : Entry α) (t : SessionTable α)
    (h : (dedup l r c t).1 = .keep s) : (dedup l r c t).2 = t := by
  unfold dedup at h ⊢
  -- One bullet per branch of `dedup`: the commit branches contradict
  -- `h`, and the keep branches return `t` as it is.
  split
  · simp_all
  · split
    · simp_all
    · split
      · split
        · rfl
        · simp_all
      · rfl

end Libp2p.Host
