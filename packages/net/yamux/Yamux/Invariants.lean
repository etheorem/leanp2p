import Yamux.Core

/-!
# The invariants of the core

The core keeps six facts about its stream table, and this module proves
them over `step` (ARCHITECTURE §3.3, §6 layer 1):

* **The window.** The bytes a stream holds unread, plus the credit the
  peer still holds, stay within the window. The stream state carries
  the fact (`StreamState.windowOk`), so `step` cannot build a state
  that breaks it. `stepWindow` restates it for every state after a
  step, and `recvDataWindow` shows the check that makes the proof
  possible: a data frame beyond the window is an error.
* **The bounded inbox.** A stream's inbox holds at most `inboxChunks`
  chunks, and the bytes in it and held behind it are bytes the window
  charged (`StreamState.slotsLe`, `StreamState.bufferedLe`);
  `stepInbox` restates both after a step. These facts are about the
  core's count of the inbox. The shell keeps the real `Chan` in step
  with the count; the core cannot see the `Chan`, so the suite tests
  that part.
* **No byte is dropped.** In every reachable state, the bytes of the
  data frame still to come are charged to the stream they go to
  (`RxOk`, `Reachable.rxOk`). So each chunk fits beside the bytes the
  reader holds, and `offer` keeps every byte of it (`offerKeeps`).
* **Parity.** A stream we opened has our parity, and a stream the peer
  opened has the other one (`parityIff`). The id carries its opener
  and its parity (`StreamId`), so every table of every state has the
  fact; `stepParity` states it after a step.
* **Retirement.** An entry exists only while one of its directions is
  open (`Inv.live`). An id that we opened and that left the table never
  comes back (`stepRetired`): our counter only grows. The peer numbers
  its own streams, and may open one of its ids again after it retired.
  The key of a stream, its id with its epoch, never comes back
  (`stepRetiredKey`), so an event that a handle of a retired stream
  posts changes nothing (`stepStale`).
* **The inbound cap.** The live streams the peer opened stay within
  `maxIncomingStreams` (`Inv.backlog`).

## How the proofs go

`step` changes the table through three operations only: `State.put`
stores a new state under an id already in the table, `State.addLocal`
adds our next stream, and `State.addRemote` adds a stream the peer
opened. Every other update leaves the table, the counters, and the role
alone (`Steps.ofFields`). Each operation gets a lemma of the form
`Steps s s'`: it keeps `Inv`, and it keeps the step relation `Grows`.
`Grows` says what a step may do: the role stays, the two counters only
grow, and every entry after the step either was in the table before,
with its id and epoch, or is fresh. `Steps` composes, so each handler
of the core is a composition of the operation lemmas, and `step`
follows. The entry operations return a `StreamState` alone, so none of
them can change an id or an epoch, and no lemma has to show it.

`RxOk` links the receive cursor to the table, so `Steps` cannot carry
it: a move of the cursor alone can break it. Its proof follows the
handlers one by one (`rxOkStep`).
-/

set_option autoImplicit false

namespace Yamux

open State

/-! ## Parity, by construction -/

/-- A stream is ours exactly when its id has our parity. The `StreamId`
of every entry carries the fact, so it holds in every state. -/
theorem parityIff (s : State) :
    ∀ e ∈ s.streams, (e.id.opener = s.role ↔ e.id.val % 2 = s.role.parity) := by
  intro e _
  rw [e.id.parity]
  exact ⟨fun h => h ▸ rfl, Role.eqOfParityEq⟩

/-- The id of a SYN the core accepts names the peer as its opener. -/
theorem StreamId.ofRemote?Some {role : Role} {n : Nat} {hlt : n < streamIdLimit} {sid : StreamId}
    (h : StreamId.ofRemote? role n hlt = some sid) : sid.opener ≠ role ∧ sid.val = n := by
  unfold StreamId.ofRemote? at h
  split at h
  · cases h
    exact ⟨by cases role <;> simp [Role.other], rfl⟩
  · cases h

/-- Two stream ids with one value are one id: the value fixes the
parity, so the opener, and the rest are proofs. -/
theorem StreamId.eqOfVal {a b : StreamId} (h : a.val = b.val) : a = b := by
  have ho : a.opener = b.opener := Role.eqOfParityEq (by rw [← a.parity, ← b.parity, h])
  cases a
  cases b
  simp only at h ho
  subst h
  subst ho
  rfl

/-- A stream the peer opened does not have our parity. -/
theorem StreamId.parityNe {sid : StreamId} {role : Role} (h : sid.opener ≠ role) :
    sid.val % 2 ≠ role.parity := by
  intro hp
  rw [sid.parity] at hp
  exact h (Role.eqOfParityEq hp)

/-! ## The invariant and the step relation -/

/-- An entry is fresh for `s`: its id is the peer's, or ours at or
above our counter, and its epoch is at or above the epoch counter. -/
def State.Fresh (s : State) (e : Entry) : Prop :=
  (e.id.opener ≠ s.role ∨ s.nextLocal ≤ e.id.val) ∧ s.nextEpoch ≤ e.epoch

/-- The facts about the table that every reachable state keeps. -/
structure Inv (s : State) : Prop where
  /-- Every id we opened is below our counter. -/
  below : ∀ e ∈ s.streams, e.id.opener = s.role → e.id.val < s.nextLocal
  /-- An entry exists only while one of its directions is open, or
  while bytes and the EOF still wait for the reader. -/
  live : ∀ e ∈ s.streams, e.state.live = true
  /-- The live streams the peer opened stay within the inbound cap. -/
  backlog : inboundCount s.role s.streams ≤ maxIncomingStreams
  /-- Every epoch in the table is below the epoch counter. -/
  epochLt : ∀ e ∈ s.streams, e.epoch < s.nextEpoch

/-- What one step may change: the role stays, the counters grow, and
every entry was in the table before, with its id and epoch, or is
fresh. -/
structure Grows (s s' : State) : Prop where
  role : s'.role = s.role
  localLe : s.nextLocal ≤ s'.nextLocal
  epochLe : s.nextEpoch ≤ s'.nextEpoch
  origin : ∀ e ∈ s'.streams, (∃ e0 ∈ s.streams, e0.id = e.id ∧ e0.epoch = e.epoch) ∨ s.Fresh e

/-- A step from `s` to `s'` keeps the invariant and the relation. -/
structure Steps (s s' : State) : Prop where
  inv : Inv s → Inv s'
  grows : Grows s s'

/-- An entry fresh for a later state is fresh for an earlier one. -/
theorem Grows.freshBack {s s' : State} (g : Grows s s') {e : Entry} (h : s'.Fresh e) :
    s.Fresh e := by
  unfold State.Fresh at h ⊢
  rw [g.role] at h
  have := g.localLe
  have := g.epochLe
  obtain ⟨hid, hep⟩ := h
  refine ⟨?_, by omega⟩
  rcases hid with h | h
  · exact .inl h
  · exact .inr (by omega)

private theorem Steps.refl (s : State) : Steps s s :=
  ⟨id, ⟨rfl, Nat.le_refl _, Nat.le_refl _, fun e he => .inl ⟨e, he, rfl, rfl⟩⟩⟩

private theorem Steps.trans {s1 s2 s3 : State} (h12 : Steps s1 s2) (h23 : Steps s2 s3) : Steps s1 s3 := by
  refine ⟨fun h => h23.inv (h12.inv h), ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [h23.grows.role, h12.grows.role]
  · exact Nat.le_trans h12.grows.localLe h23.grows.localLe
  · exact Nat.le_trans h12.grows.epochLe h23.grows.epochLe
  · intro e he
    rcases h23.grows.origin e he with ⟨e1, he1, hid, hep⟩ | hfresh
    · rcases h12.grows.origin e1 he1 with ⟨e0, he0, hid0, hep0⟩ | hfresh1
      · exact .inl ⟨e0, he0, hid0.trans hid, hep0.trans hep⟩
      · right
        unfold State.Fresh at hfresh1 ⊢
        rw [← hid, ← hep]
        exact hfresh1
    · exact .inr (h12.grows.freshBack hfresh)

/-- An update that leaves the table, the counters, and the role alone. -/
theorem Steps.ofFields {s s' : State} (hr : s'.role = s.role) (hst : s'.streams = s.streams)
    (hl : s'.nextLocal = s.nextLocal) (hn : s'.nextEpoch = s.nextEpoch) : Steps s s' := by
  refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, ⟨hr, by omega, by omega, ?_⟩⟩
  · intro e he ho
    rw [hst] at he
    rw [hr] at ho
    rw [hl]
    exact h.below e he ho
  · rw [hst]; exact h.live
  · rw [hst, hr]; exact h.backlog
  · intro e he
    rw [hst] at he
    rw [hn]
    exact h.epochLt e he
  · intro e he
    rw [hst] at he
    exact .inl ⟨e, he, rfl, rfl⟩

/-- A move of the receive cursor. -/
theorem Steps.rx (s : State) (r : Rx) : Steps s { s with rx := r } :=
  Steps.ofFields rfl rfl rfl rfl

/-! ## List lemmas -/

private theorem countPMapEq {α : Type} (p : α → Bool) (f : α → α) :
    ∀ (l : List α), (∀ x ∈ l, p (f x) = p x) → (l.map f).countP p = l.countP p
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, List.countP_cons, h x (by simp)]
    rw [countPMapEq p f l (fun y hy => h y (by simp [hy]))]

private theorem countPFilterLe {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (l.filter q).countP p ≤ l.countP p
  | [] => Nat.le_refl _
  | x :: l => by
    have ih := countPFilterLe p q l
    cases hq : q x <;> cases hp : p x <;> simp [hq, hp] <;> omega

/-! ## The table operations -/

theorem find?Mem {s : State} {id : Nat} {e : Entry} (h : s.find? id = some e) :
    e ∈ s.streams ∧ e.id.val = id := by
  unfold State.find? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa [State.byId] using List.find?_some h⟩

private theorem find?None {s : State} {id : Nat} (h : s.find? id = none) :
    ∀ e ∈ s.streams, e.id.val ≠ id := by
  unfold State.find? at h
  intro e he hid
  have := List.find?_eq_none.mp h e he
  simp [State.byId, hid] at this

/-- Storing a new state under an entry of the table. -/
theorem stepsPut {s : State} {e : Entry} (he : e ∈ s.streams) (st : StreamState) :
    Steps s (s.put e st) := by
  unfold State.put
  split
  · next hlive =>
    refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩⟩
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      split
      · exact h.below e he
      · exact h.below y hy
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      split
      · exact hlive
      · exact h.live y hy
    · -- The entry keeps its id, so its opener, and the count of inbound
      -- entries does not move.
      unfold inboundCount
      rw [countPMapEq]
      · exact h.backlog
      · intro y _
        split
        · next hyid => simp only [hyid]
        · rfl
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      split
      · exact h.epochLt e he
      · exact h.epochLt y hy
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      split
      · exact .inl ⟨e, he, rfl, rfl⟩
      · exact .inl ⟨y, hy, rfl, rfl⟩
  · refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩⟩
    · intro x hx; exact h.below x (List.mem_filter.mp hx).1
    · intro x hx; exact h.live x (List.mem_filter.mp hx).1
    · exact Nat.le_trans (countPFilterLe _ _ _) h.backlog
    · intro x hx; exact h.epochLt x (List.mem_filter.mp hx).1
    · intro x hx; exact .inl ⟨x, (List.mem_filter.mp hx).1, rfl, rfl⟩

private theorem stepsAddLocal (s : State) (hlt : s.nextLocal < streamIdLimit) :
    Steps s (s.addLocal hlt) := by
  unfold State.addLocal
  refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, by simp, by simp, ?_⟩⟩
  · intro x hx ho
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have := h.below x hx ho
      simp only
      omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact h.live x hx
  · simpa [inboundCount, List.countP_cons] using h.backlog
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have := h.epochLt x hx
      simp only
      omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · right
      unfold State.Fresh
      exact ⟨.inr (Nat.le_refl _), Nat.le_refl _⟩
    · exact .inl ⟨x, hx, rfl, rfl⟩

/-- Adding a stream the peer opened, under the checks of `recvStream`:
the peer's id, and room under the inbound cap. -/
theorem stepsAddRemote {s : State} {sid : StreamId} (st : StreamState)
    (hpeer : sid.opener ≠ s.role)
    (hroom : inboundCount s.role s.streams < maxIncomingStreams) : Steps s (s.addRemote sid st) := by
  unfold State.addRemote
  refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, Nat.le_refl _, by simp, ?_⟩⟩
  · intro x hx ho
    split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd ho hpeer
      · exact h.below x hx ho
    · exact h.below x hx ho
  · intro x hx
    split at hx
    · next hlive =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hlive
      · exact h.live x hx
    · exact h.live x hx
  · split
    · simp only [inboundCount, List.countP_cons] at hroom ⊢
      simp only [bne_iff_ne, ne_eq, hpeer, not_false_eq_true, ↓reduceIte]
      omega
    · exact h.backlog
  · intro x hx
    split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have := h.epochLt x hx
        simp only
        omega
    · have := h.epochLt x hx
      simp only
      omega
  · intro x hx
    split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · right
        unfold State.Fresh
        exact ⟨.inl hpeer, Nat.le_refl _⟩
      · exact .inl ⟨x, hx, rfl, rfl⟩
    · exact .inl ⟨x, hx, rfl, rfl⟩

/-! ## The handlers -/

theorem stepsOpenNow (s : State) (tag : Nat) : Steps s (openNow s tag).1 := by
  unfold openNow
  split
  · next hlt => exact stepsAddLocal s hlt
  · exact Steps.refl s

private theorem stepsOpenPending (l : List Nat) :
    ∀ (s : State) (acts : Array Action), Steps s (openPending s l acts).1 := by
  induction l with
  | nil => intro s acts; exact Steps.ofFields rfl rfl rfl rfl
  | cons tag rest ih =>
    intro s acts
    simp only [openPending]
    split
    · exact (stepsOpenNow s tag).trans (ih _ _)
    · exact Steps.ofFields rfl rfl rfl rfl

private theorem stepsOnOpen (s : State) (tag : Nat) : Steps s (onOpen s tag).1 := by
  unfold onOpen
  split
  · exact Steps.refl s
  · split
    · exact stepsOpenNow s tag
    · exact Steps.ofFields rfl rfl rfl rfl

private theorem stepsOnEntry (s : State) (p : Entry → Bool) (f : Entry → StreamState × Array Action)
    (missing : Array Action) : Steps s (onEntry s p f missing).1 := by
  unfold onEntry
  split
  · exact Steps.refl s
  · next e he => exact stepsPut (List.mem_of_find?_eq_some he) _

private theorem stepsOnGoAway (s : State) : Steps s (onGoAway s).1 := by
  unfold onGoAway
  split
  · exact Steps.refl s
  · exact Steps.ofFields rfl rfl rfl rfl

private theorem stepsOnPing (s : State) (tag : Nat) : Steps s (onPing s tag).1 :=
  Steps.ofFields rfl rfl rfl rfl

private theorem stepsRecvPing (s : State) (h : Header) : Steps s (recvPing s h).1 := by
  unfold recvPing
  split
  · exact Steps.refl s
  · split
    · split
      · dsimp only
        split <;> exact Steps.ofFields rfl rfl rfl rfl
      · exact Steps.refl s
    · exact Steps.refl s

private theorem stepsRecvGoAway {s s' : State} {h : Header} {acts : Array Action}
    (hr : recvGoAway s h = .ok (s', acts)) : Steps s s' := by
  unfold recvGoAway at hr
  split at hr
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Steps.refl s
  · cases hr
  · cases hr

private theorem stepsRecvStream {s s' : State} {h : Header} {acts : Array Action}
    (hr : recvStream s h = .ok (s', acts)) : Steps s s' := by
  unfold recvStream at hr
  simp only at hr
  split at hr
  · cases hr
  · split at hr
    · -- A SYN. An id the peer may not open is an error.
      split at hr
      · cases hr
      · next sid hsid =>
        obtain ⟨hpeer, hval⟩ := StreamId.ofRemote?Some hsid
        split at hr
        · cases hr
        · split at hr
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, -⟩ := hr
            exact Steps.ofFields rfl rfl rfl rfl
          · next hroom =>
            split at hr
            · cases hr
            · next st a rx _ =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, -⟩ := hr
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hroom
              refine (stepsAddRemote st hpeer (by omega)).trans ?_
              exact Steps.ofFields rfl rfl rfl rfl
    · -- No SYN: a frame for a live stream, or for nothing.
      split at hr
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, -⟩ := hr
        exact Steps.ofFields rfl rfl rfl rfl
      · next e he =>
        split at hr
        · cases hr
        · next st a rx _ =>
          have hput := (stepsPut (find?Mem he).1 st).trans (Steps.rx _ rx)
          split at hr
          · simp only [Except.ok.injEq] at hr
            have h1 := congrArg Prod.fst hr
            simp only at h1
            rw [← h1]
            exact hput.trans (stepsOpenPending _ _ _)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, -⟩ := hr
            exact hput

private theorem stepsRecvHeader {s s' : State} {h : Header} {acts : Array Action}
    (hr : recvHeader s h = .ok (s', acts)) : Steps s s' := by
  unfold recvHeader at hr
  split at hr
  · exact stepsRecvStream hr
  · exact stepsRecvStream hr
  · simp only [Except.ok.injEq] at hr
    have h1 := congrArg Prod.fst hr
    simp only at h1
    rw [← h1]
    exact stepsRecvPing s h
  · exact stepsRecvGoAway hr

private theorem stepsFinishPayload (s : State) (id : Nat) (deliver fin : Bool) :
    Steps s (finishPayload s id deliver fin).1 := by
  unfold finishPayload
  split
  · exact stepsOnEntry _ _ _ _
  · exact Steps.refl s

private theorem stepsRecvChunk (s : State) (id : Nat) (chunk : ByteArray) (deliver : Bool) :
    Steps s (recvChunk s id chunk deliver).1 := by
  unfold recvChunk
  split
  · exact stepsOnEntry _ _ _ _
  · exact Steps.refl s

private theorem stepsRecvBytes (fuel : Nat) :
    ∀ {s s' : State} {b : ByteArray} {pos : Nat} {acts acts' : Array Action},
      recvBytes fuel s b pos acts = .ok (s', acts') → Steps s s' := by
  induction fuel with
  | zero =>
    intro s s' b pos acts acts' hr
    simp only [recvBytes, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Steps.refl s
  | succ fuel ih =>
    intro s s' b pos acts acts' hr
    simp only [recvBytes] at hr
    split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact Steps.refl s
    · split at hr
      · -- Between frames.
        split at hr
        · split at hr
          · cases hr
          · split at hr
            · cases hr
            · next s1 a1 h1 =>
              exact (Steps.rx s _).trans ((stepsRecvHeader h1).trans (ih hr))
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, -⟩ := hr
          exact Steps.rx s _
      · -- Inside a payload.
        split at hr
        · exact (stepsRecvChunk s _ _ _).trans
            ((stepsFinishPayload _ _ _ _).trans ((Steps.rx _ _).trans (ih hr)))
        · exact (stepsRecvChunk s _ _ _).trans ((Steps.rx _ _).trans (ih hr))

/-! The timers (`Yamux/Core.lean`, "Time") change no stream, no counter,
and no cursor, so each of their operations is a step of the relation. -/

theorem stepsHeard (s : State) (p : Bytes.Blob) : Steps s (heard s p) := by
  unfold heard
  split
  · exact Steps.refl s
  · exact Steps.ofFields rfl rfl rfl rfl

private theorem stepsSchedule (s : State) (a : Array Action) : Steps s (schedule s a).1 := by
  unfold schedule
  dsimp only
  split
  · exact Steps.refl s
  · split <;> exact Steps.ofFields rfl rfl rfl rfl

private theorem stepsOnTick (s : State) (t : Nat) : Steps s (onTick s t).1 := by
  unfold onTick sendPing
  dsimp only
  split
  · split <;> exact Steps.ofFields rfl rfl rfl rfl
  · exact Steps.ofFields rfl rfl rfl rfl

/-- Every step keeps the invariant and the step relation. -/
theorem stepsStep {s s' : State} {ev : Event} {acts : List Action}
    (hr : step s ev = .ok (s', acts)) : Steps s s' := by
  cases ev with
  | bytes p =>
    simp only [step] at hr
    cases hb : recvBytes (p.bytes.size + 1) (heard s p) p.bytes 0 #[] with
    | error e => simp [hb, Except.map] at hr
    | ok r =>
      obtain ⟨s1, a1⟩ := r
      simp only [hb, Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact (stepsHeard s p).trans ((stepsRecvBytes _ hb).trans (stepsSchedule s1 a1))
  | eof =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact Steps.refl s
  | tick t =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (stepsOnTick s t).trans (stepsSchedule _ _)
  | openStream tag =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact stepsOnOpen s tag
  | write k tag p =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact stepsOnEntry _ _ _ _
  | consumed k n =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact stepsOnEntry _ _ _ _
  | close k =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact stepsOnEntry _ _ _ _
  | reset k =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact stepsOnEntry _ _ _ _
  | ping tag =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (stepsOnPing s tag).trans (stepsSchedule _ _)
  | goAway =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact stepsOnGoAway s

/-! ## The theorems -/

/-- A new session keeps the invariant. -/
theorem Inv.new (r : Role) : Inv (State.new r) where
  below := by simp [State.new]
  live := by simp [State.new]
  backlog := by simp [State.new, inboundCount, maxIncomingStreams]
  epochLt := by simp [State.new]

/-- Every step keeps the invariant. -/
theorem stepInv {s s' : State} {ev : Event} {acts : List Action} (hs : Inv s)
    (hr : step s ev = .ok (s', acts)) : Inv s' :=
  (stepsStep hr).inv hs

/-- The states a session reaches from its start. -/
inductive Reachable (r : Role) : State → Prop where
  | new : Reachable r (State.new r)
  | step {s s' : State} {ev : Event} {acts : List Action} :
      Reachable r s → step s ev = .ok (s', acts) → Reachable r s'

/-- Every reachable state keeps the invariant. -/
theorem Reachable.inv {r : Role} {s : State} (h : Reachable r s) : Inv s := by
  induction h with
  | new => exact Inv.new r
  | step _ hstep ih => exact stepInv ih hstep

/-- The window theorem: every stream holds no more unread bytes plus
peer credit than the window, so the receive window never goes negative,
and a stream never buffers past it. The fact holds by construction, for
every state: the stream state carries it, and the step hypothesis only
names the state of interest. -/
theorem stepWindow {s s' : State} {ev : Event} {acts : List Action}
    (_hr : step s ev = .ok (s', acts)) :
    ∀ e ∈ s'.streams, e.state.recvWindow + e.state.unread ≤ initialWindow :=
  fun e _ => e.state.windowOk

/-- The inbox theorem: every stream's inbox holds at most `inboxChunks`
chunks, and the bytes in it plus the bytes held behind it plus the
peer's credit stay within the window. So a stream buffers at most
256 KiB, in at most `inboxChunks` chunks plus one held chunk, whatever
the peer sends. The fact holds by construction, for every state, as
for `stepWindow`. It bounds the core's count; the shell's `Chan`
follows the count, and the suite tests that. -/
theorem stepInbox {s s' : State} {ev : Event} {acts : List Action}
    (_hr : step s ev = .ok (s', acts)) :
    ∀ e ∈ s'.streams, e.state.slots ≤ inboxChunks ∧
      e.state.inInbox + e.state.held.bytes.size + e.state.recvWindow ≤ initialWindow :=
  fun e _ => ⟨e.state.slotsLe, by have := e.state.bufferedLe; have := e.state.windowOk; omega⟩

/-- The check behind the window fact: the body of a data frame longer
than the stream's receive window is an error, before any payload byte.
`Entry.onFrame` runs it for every data frame without RST. -/
theorem recvDataWindow {id : Nat} {st : StreamState} {h : Header}
    (hlen : st.recvWindow < h.length) : ∃ err, Entry.recvData id st h = .error err := by
  unfold Entry.recvData
  simp only [Nat.not_le.mpr hlen, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- A data frame longer than the initial window is an error whatever
its stream: no stream ever holds more credit (§5.1). -/
theorem recvStreamLong {s : State} {h : Header} (hd : h.type = .data)
    (hlen : initialWindow < h.length) :
    recvStream s h = .error (.windowExceeded h.streamId h.length initialWindow) := by
  unfold recvStream
  simp [hd, hlen]

/-- The parity theorem: after any step, our streams have our parity and
the peer's have the other. -/
theorem stepParity {s s' : State} {ev : Event} {acts : List Action}
    (hr : step s ev = .ok (s', acts)) :
    ∀ e ∈ s'.streams, (e.id.opener = s.role ↔ e.id.val % 2 = s.role.parity) := by
  rw [← (stepsStep hr).grows.role]
  exact parityIff s'

/-- One of our ids is retired: it has our parity, it is below our
counter, so we opened it, and no live stream has it. -/
def Retired (s : State) (k : Nat) : Prop :=
  k % 2 = s.role.parity ∧ k < s.nextLocal ∧ ∀ e ∈ s.streams, e.id.val ≠ k

/-- A retired id of ours is never reused: it stays retired after any
step. The peer's ids are the peer's to number; parity keeps them apart
from ours. -/
theorem stepRetired {s s' : State} {ev : Event} {acts : List Action} {k : Nat}
    (hr : step s ev = .ok (s', acts)) (hk : Retired s k) : Retired s' k := by
  have hst := stepsStep hr
  have hrole := hst.grows.role
  have hl := hst.grows.localLe
  obtain ⟨hpar, hbelow, hnone⟩ := hk
  refine ⟨by rw [hrole]; exact hpar, by omega, ?_⟩
  intro e he hek
  rcases hst.grows.origin e he with ⟨e0, he0, hid, -⟩ | hfresh
  · exact hnone e0 he0 (by rw [hid]; exact hek)
  · -- A fresh entry is the peer's, which has the other parity, or ours
    -- at or above our counter; a retired id is ours and below it.
    have hp := parityIff s' e he
    rw [hrole] at hp
    subst hek
    unfold State.Fresh at hfresh
    rcases hfresh.1 with hpeer | hge
    · exact hpeer (hp.mpr hpar)
    · omega

/-! ## Stream keys -/

/-- The key of a stream that has retired: its epoch is below the
counter, so the stream existed, and no live stream has the key. -/
def RetiredKey (s : State) (k : StreamKey) : Prop :=
  k.epoch < s.nextEpoch ∧ ∀ e ∈ s.streams, e.key ≠ k

/-- A retired key never comes back, ours or the peer's: a new stream
takes a new epoch. The peer may open an id again, and the new stream
still has a new key. -/
theorem stepRetiredKey {s s' : State} {ev : Event} {acts : List Action} {k : StreamKey}
    (hr : step s ev = .ok (s', acts)) (hk : RetiredKey s k) : RetiredKey s' k := by
  have hst := stepsStep hr
  obtain ⟨hlt, hnone⟩ := hk
  refine ⟨by have := hst.grows.epochLe; omega, ?_⟩
  intro e he hek
  subst hek
  rcases hst.grows.origin e he with ⟨e0, he0, hid, hep⟩ | hfresh
  · exact hnone e0 he0 (by unfold Entry.key; rw [hid, hep])
  · unfold State.Fresh at hfresh
    have h1 := hfresh.2
    have h2 : e.key.epoch = e.epoch := rfl
    omega

/-- An event of the application under a key that no live stream has
changes nothing: the state stays, no frame goes out, and a write is
refused. So the handle of a retired stream cannot reach a later stream
on the same id (`stepRetiredKey`). -/
theorem stepStale {s : State} {k : StreamKey} {n tag : Nat} {p : Bytes.Blob}
    (hk : ∀ e ∈ s.streams, e.key ≠ k) :
    step s (.consumed k n) = .ok (s, []) ∧ step s (.close k) = .ok (s, []) ∧
      step s (.reset k) = .ok (s, []) ∧ step s (.write k tag p) = .ok (s, [.refused tag .closed]) := by
  have hnone : s.streams.find? (State.byKey k) = none := by
    rw [List.find?_eq_none]
    intro e he
    simp [State.byKey, hk e he]
  simp [step, onEntry, hnone]

/-! ## No byte is dropped -/

/-- The bytes `rem` that are still to come on a stream that reads are
charged: they fit in its unread count beside the bytes the reader holds
or waits for. -/
def Charged (rem : Nat) (st : StreamState) : Prop :=
  (st.recvOpen || st.eofDue) = true → st.inInbox + st.held.bytes.size + rem ≤ st.unread

/-- The receive cursor and the table agree. Inside a data payload that
goes to its stream, the bytes still to come are charged to every live
stream with the id, and an id of our parity is one we opened. -/
def RxOk (s : State) : Prop :=
  ∀ id rem fin, s.rx = .payload id rem true fin →
    (id % 2 = s.role.parity → id < s.nextLocal) ∧ ∀ e ∈ s.streams, e.id.val = id → Charged rem e.state

private theorem Charged.mono {rem rem' : Nat} {st : StreamState} (h : Charged rem st) (hle : rem' ≤ rem) :
    Charged rem' st := by
  intro hr
  have := h hr
  omega

/-- A chunk that fits beside the held bytes is kept whole: every byte of
it lands in the inbox or behind it. With `Reachable.rxOk`, this is the
proof that the `else` arm of `offer` never runs. -/
theorem offerKeeps {st : StreamState} {id : Nat} {chunk : ByteArray}
    (h : st.inInbox + st.held.bytes.size + chunk.size ≤ st.unread) :
    (st.offer id chunk).1.inInbox + (st.offer id chunk).1.held.bytes.size =
      st.inInbox + st.held.bytes.size + chunk.size := by
  unfold StreamState.offer
  split
  · split
    · show st.inInbox + chunk.size + st.held.bytes.size = _
      omega
    · show st.inInbox + (st.held.bytes ++ chunk).size = _
      simp only [ByteArray.size_append]
      omega
  · next hk => exact absurd h hk

/-- `offer` leaves the unread count alone: `recvData` charged the bytes
already. -/
theorem offerUnread (st : StreamState) (id : Nat) (chunk : ByteArray) :
    (st.offer id chunk).1.unread = st.unread := by
  unfold StreamState.offer
  split
  · split <;> rfl
  · rfl

/-- An entry after `put`: the stored one, or an entry of the table with
another id. -/
theorem memPut {s : State} {e x : Entry} {st : StreamState} (hx : x ∈ (s.put e st).streams) :
    (x.id = e.id ∧ x.state = st) ∨ (x ∈ s.streams ∧ x.id ≠ e.id) := by
  unfold State.put at hx
  split at hx
  · simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    by_cases hyid : y.id = e.id
    · left
      simp [hyid]
    · right
      simp only [hyid, ↓reduceIte]
      exact ⟨hy, hyid⟩
  · right
    exact ⟨(List.mem_filter.mp hx).1, of_decide_eq_true (List.mem_filter.mp hx).2⟩

/-- An entry after `onEntry`: one of the table, or one after the `put`
of the picked entry. -/
theorem memOnEntry {s : State} {p : Entry → Bool} {f : Entry → StreamState × Array Action}
    {missing : Array Action} {x : Entry} (hx : x ∈ (onEntry s p f missing).1.streams) :
    x ∈ s.streams ∨ ∃ e ∈ s.streams, p e = true ∧ x ∈ (s.put e (f e).1).streams := by
  unfold onEntry at hx
  split at hx
  · exact .inl hx
  · next e he => exact .inr ⟨e, List.mem_of_find?_eq_some he, List.find?_some he, hx⟩

/-- A state whose cursor delivers no payload agrees with its table. -/
theorem rxOkOfRx {s : State} (h : ∀ id rem fin, s.rx ≠ .payload id rem true fin) : RxOk s :=
  fun id rem fin hrx => absurd hrx (h id rem fin)

/-- An update that leaves the cursor, the table, the role, and our
counter alone keeps the agreement. -/
theorem rxOkOfFields {s s' : State} (hrx : s'.rx = s.rx) (hst : s'.streams = s.streams)
    (hr : s'.role = s.role) (hl : s'.nextLocal = s.nextLocal) (h : RxOk s) : RxOk s' := by
  intro id rem fin hp
  rw [hrx] at hp
  rw [hst, hr, hl]
  exact h id rem fin hp

private theorem rxOkPut {s : State} {e : Entry} (he : e ∈ s.streams) {st : StreamState}
    (hc : ∀ rem, Charged rem e.state → Charged rem st) (h : RxOk s) : RxOk (s.put e st) := by
  unfold State.put
  split
  · intro id rem fin hp
    obtain ⟨hpar, hall⟩ := h id rem fin hp
    refine ⟨hpar, ?_⟩
    intro x hx hxid
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    split at hxid
    · next =>
      split
      · exact hc rem (hall e he hxid)
      · contradiction
    · split
      · contradiction
      · exact hall y hy hxid
  · intro id rem fin hp
    obtain ⟨hpar, hall⟩ := h id rem fin hp
    exact ⟨hpar, fun x hx hxid => hall x (List.mem_filter.mp hx).1 hxid⟩

private theorem rxOkAddLocal {s : State} (hlt : s.nextLocal < streamIdLimit) (h : RxOk s) :
    RxOk (s.addLocal hlt) := by
  intro id rem fin hp
  obtain ⟨hpar, hall⟩ := h id rem fin hp
  refine ⟨fun hpi => by have := hpar hpi; show id < s.nextLocal + 2; omega, ?_⟩
  intro x hx hxid
  simp only [State.addLocal, List.mem_cons] at hx
  rcases hx with rfl | hx
  · -- The new entry has our next id, which no payload names.
    have hval : s.nextLocal = id := hxid
    have := hpar (by rw [← hval]; exact s.nextLocalParity)
    omega
  · exact hall x hx hxid

private theorem rxOkOpenNow (s : State) (tag : Nat) (h : RxOk s) : RxOk (openNow s tag).1 := by
  unfold openNow
  split
  · exact rxOkAddLocal _ h
  · exact h

private theorem rxOkOpenPending (l : List Nat) :
    ∀ (s : State) (acts : Array Action), RxOk s → RxOk (openPending s l acts).1 := by
  induction l with
  | nil => intro s acts h; exact rxOkOfFields rfl rfl rfl rfl h
  | cons tag rest ih =>
    intro s acts h
    simp only [openPending]
    split
    · exact ih _ _ (rxOkOpenNow s tag h)
    · exact rxOkOfFields rfl rfl rfl rfl h

private theorem rxOkOnOpen (s : State) (tag : Nat) (h : RxOk s) : RxOk (onOpen s tag).1 := by
  unfold onOpen
  split
  · exact h
  · split
    · exact rxOkOpenNow s tag h
    · exact rxOkOfFields rfl rfl rfl rfl h

private theorem rxOkOnEntry {s : State} {p : Entry → Bool} {f : Entry → StreamState × Array Action}
    {missing : Array Action} (hf : ∀ e rem, Charged rem e.state → Charged rem (f e).1)
    (h : RxOk s) : RxOk (onEntry s p f missing).1 := by
  unfold onEntry
  split
  · exact h
  · next e he => exact rxOkPut (List.mem_of_find?_eq_some he) (hf e) h

/-! ### The entry operations keep the charge -/

theorem chargedWrite (e : Entry) (tag : Nat) (p : Bytes.Blob) (rem : Nat)
    (h : Charged rem e.state) : Charged rem (e.write tag p).1 := by
  unfold Entry.write
  dsimp only
  split
  · exact h
  · exact h

private theorem chargedFlush {rem : Nat} {st : StreamState} (id : Nat) (h : Charged rem st) :
    Charged rem (st.flush id).1 := by
  unfold StreamState.flush
  split
  · intro hr
    have hr' : (st.recvOpen || st.eofDue) = true := by
      simp only [Bool.or_false] at hr
      simp [hr]
    have := h hr'
    show st.inInbox + st.held.bytes.size + ByteArray.empty.size + rem ≤ st.unread
    simp only [ByteArray.size_empty]
    omega
  · exact h

private theorem chargedTake {rem : Nat} {st : StreamState} (n : Nat) (h : Charged rem st) :
    Charged rem (st.take n) := by
  intro hr
  have := h hr
  show st.inInbox - min n st.inInbox + st.held.bytes.size + rem ≤ st.unread - min n st.inInbox
  omega

private theorem chargedConsume (e : Entry) (n rem : Nat) (h : Charged rem e.state) :
    Charged rem (e.consume n).1 := by
  unfold Entry.consume
  split
  · next st moved hfl =>
    have hst : Charged rem st := by
      have := chargedFlush e.id.val (chargedTake n h)
      rw [hfl] at this
      exact this
    split
    · intro hr
      exact hst hr
    · exact hst

private theorem chargedCloseLocal (e : Entry) (rem : Nat) (h : Charged rem e.state) :
    Charged rem e.closeLocal.1 := by
  unfold Entry.closeLocal
  dsimp only
  split
  · exact h
  · exact h

private theorem chargedResetLocal (e : Entry) (rem : Nat) : Charged rem e.resetLocal.1 := by
  intro hr
  simp [Entry.resetLocal] at hr

/-! ### The receive path keeps the charge -/

/-- The cursor a frame of a stream leaves: a payload that goes to the
stream is the stream's own, and its bytes are charged. -/
theorem recvDataRx {id : Nat} {st st' : StreamState} {h : Header} {acts : Array Action} {rx : Rx}
    (hr : Entry.recvData id st h = .ok (st', acts, rx)) :
    ∀ id' rem fin, rx = .payload id' rem true fin → id' = id ∧ Charged rem st' := by
  intro id' rem fin hp
  unfold Entry.recvData at hr
  split at hr
  · next hw =>
    simp only at hr
    split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -, rfl⟩ := hr
      simp only [Rx.payload.injEq] at hp
      obtain ⟨rfl, rfl, hto, -⟩ := hp
      refine ⟨rfl, ?_⟩
      intro _
      have := st.bufferedLe
      show st.inInbox + st.held.bytes.size + h.length ≤
        st.unread + (if st.recvOpen || st.eofDue then h.length else 0)
      simp only [hto, ↓reduceIte]
      omega
    · split at hr <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, -, rfl⟩ := hr
        cases hp
  · cases hr

private theorem onFrameRx {role : Role} {e : Entry} {h : Header} {st : StreamState} {acts : Array Action}
    {rx : Rx} (hr : e.onFrame role h = .ok (st, acts, rx)) :
    ∀ id rem fin, rx = .payload id rem true fin → id = e.id.val ∧ Charged rem st := by
  intro id rem fin hp
  unfold Entry.onFrame at hr
  simp only at hr
  split at hr
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    split at hp <;> cases hp
  · split at hr
    · exact recvDataRx hr id rem fin hp
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, -, rfl⟩ := hr
      cases hp

/-- A skip cursor delivers nothing. -/
private theorem skipNe {b : Bool} {id len : Nat} :
    ∀ id' rem fin, (if b then Rx.payload id len false false else .header ⟨.empty⟩) ≠
      .payload id' rem true fin := by
  intro id' rem fin hp
  split at hp <;> cases hp

/-- A frame header of a data or window-update frame leaves a cursor
that agrees with the table. The cursor before it sits between frames,
so the old payload has ended, and only the new frame counts. -/
theorem rxOkRecvStream {s s' : State} {h : Header} {acts : Array Action}
    (hs : Inv s) (hr : recvStream s h = .ok (s', acts)) : RxOk s' := by
  unfold recvStream at hr
  simp only at hr
  split at hr
  · cases hr
  · split at hr
    · -- A SYN. An id the peer may not open is an error.
      split at hr
      · cases hr
      · next sid hsid =>
        obtain ⟨hpeer, hval⟩ := StreamId.ofRemote?Some hsid
        split at hr
        · cases hr
        · next hdup =>
          split at hr
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, -⟩ := hr
            exact rxOkOfRx skipNe
          · split at hr
            · cases hr
            · next st a rx hf =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, -⟩ := hr
              have hnone : s.find? h.streamId = none := by
                simpa using hdup
              intro id rem fin hp
              obtain ⟨hid, hch⟩ := onFrameRx hf id rem fin hp
              simp only at hid
              refine ⟨fun hpi => absurd (hid ▸ hpi) (StreamId.parityNe hpeer), ?_⟩
              intro x hx hxid
              simp only [State.addRemote] at hx
              split at hx
              · simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact hch
                · exact absurd (hxid.trans (hid.trans hval)) (find?None hnone x hx)
              · exact absurd (hxid.trans (hid.trans hval)) (find?None hnone x hx)
    · -- No SYN: a frame for a live stream, or for nothing.
      split at hr
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, -⟩ := hr
        exact rxOkOfRx skipNe
      · next e he =>
        obtain ⟨hmem, -⟩ := find?Mem he
        split at hr
        · cases hr
        · next st a rx hf =>
          -- The state after the frame, before a waiting open goes out.
          have hmid : RxOk { s.put e st with rx } := by
            intro id rem fin hp
            obtain ⟨hid, hch⟩ := onFrameRx hf id rem fin hp
            have hgr := (stepsPut hmem st).grows
            refine ⟨fun hpi => ?_, fun x hx hxid => ?_⟩
            · -- The id is the entry's; with our parity, we opened it.
              have hpi' : id % 2 = (s.put e st).role.parity := hpi
              rw [hgr.role, hid] at hpi'
              have := hs.below e hmem ((parityIff s e hmem).mpr hpi')
              have := hgr.localLe
              show id < (s.put e st).nextLocal
              omega
            · -- One value is one id, so the only entry with the id is
              -- the one the frame changed.
              have hx' : x ∈ (s.put e st).streams := hx
              rcases memPut hx' with ⟨-, hst⟩ | ⟨-, hne⟩
              · rw [hst]
                exact hch
              · exact absurd (StreamId.eqOfVal (hxid.trans hid)) hne
          split at hr
          · simp only [Except.ok.injEq] at hr
            have h1 := congrArg Prod.fst hr
            simp only at h1
            rw [← h1]
            exact rxOkOpenPending _ _ _ hmid
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, -⟩ := hr
            exact hmid

private theorem rxRecvPing (s : State) (h : Header) : (recvPing s h).1.rx = s.rx := by
  unfold recvPing
  split
  · rfl
  · split
    · split
      · dsimp only
        split <;> rfl
      · rfl
    · rfl

private theorem rxOkRecvHeader {s s' : State} {h : Header} {acts : Array Action}
    (hs : Inv s) (hrx : s.rx = .header ⟨.empty⟩) (h0 : RxOk s)
    (hr : recvHeader s h = .ok (s', acts)) : RxOk s' := by
  unfold recvHeader at hr
  split at hr
  · exact rxOkRecvStream hs hr
  · exact rxOkRecvStream hs hr
  · simp only [Except.ok.injEq] at hr
    have h1 := congrArg Prod.fst hr
    simp only at h1
    rw [← h1]
    exact rxOkOfRx fun id rem fin hp => by rw [rxRecvPing, hrx] at hp; cases hp
  · unfold recvGoAway at hr
    split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact h0
    · cases hr
    · cases hr

/-- A chunk of `n` bytes or fewer, inside a payload with `rem ≥ n`
bytes to come: the cursor that moves past it agrees with the table. -/
theorem rxOkChunk {s : State} {id rem n : Nat} {deliver fin : Bool} {chunk : ByteArray}
    (hrx : s.rx = .payload id rem deliver fin) (h0 : RxOk s)
    (hc : chunk.size ≤ n) (hn : n ≤ rem) :
    RxOk { (recvChunk s id chunk deliver).1 with rx := .payload id (rem - n) deliver fin } := by
  intro id' rem' fin' hp
  simp only [Rx.payload.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
  obtain ⟨hpar, hall⟩ := h0 id rem fin hrx
  have hgr := (stepsRecvChunk s id chunk true).grows
  refine ⟨fun hpi => ?_, fun x hx hxid => ?_⟩
  · have hpi' : id % 2 = (recvChunk s id chunk true).1.role.parity := hpi
    rw [hgr.role] at hpi'
    have := hpar hpi'
    have := hgr.localLe
    show id < (recvChunk s id chunk true).1.nextLocal
    omega
  · have hx' : x ∈ (recvChunk s id chunk true).1.streams := hx
    unfold recvChunk at hx'
    split at hx'
    · -- The chunk goes to the stream with the id.
      rcases memOnEntry hx' with hold | ⟨e, hmem, hpe, hxput⟩
      · exact (hall x hold hxid).mono (by omega)
      · have heid : e.id.val = id := by simpa [State.byId] using hpe
        rcases memPut hxput with ⟨-, hst⟩ | ⟨hold, -⟩
        · rw [hst]
          show Charged (rem - n) (if (e.state.recvOpen || e.state.eofDue) = true then
            e.state.offer e.id.val chunk else (e.state, #[])).1
          split
          · -- The stream reads: the chunk fits, so `offer` keeps it.
            next hread =>
            have h1 := hall e hmem heid hread
            have hfit : e.state.inInbox + e.state.held.bytes.size + chunk.size ≤ e.state.unread := by
              omega
            intro _
            have := offerKeeps (id := e.id.val) hfit
            have := offerUnread e.state e.id.val chunk
            omega
          · next hread =>
            intro hr
            exact absurd hr hread
        · exact (hall x hold hxid).mono (by omega)
    · exact (hall x hx' hxid).mono (by omega)

private theorem rxOkRecvBytes (fuel : Nat) :
    ∀ {s s' : State} {b : ByteArray} {pos : Nat} {acts acts' : Array Action},
      Inv s → RxOk s → recvBytes fuel s b pos acts = .ok (s', acts') → RxOk s' := by
  induction fuel with
  | zero =>
    intro s s' b pos acts acts' _ h0 hr
    simp only [recvBytes, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact h0
  | succ fuel ih =>
    intro s s' b pos acts acts' hs h0 hr
    simp only [recvBytes] at hr
    split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact h0
    · next hpos =>
      split at hr
      · -- Between frames.
        split at hr
        · split at hr
          · cases hr
          · split at hr
            · cases hr
            · next s1 a1 h1 =>
              have hs1 := (Steps.rx s (.header ⟨.empty⟩)).inv hs
              have hstep := (stepsRecvHeader h1).inv hs1
              have h01 : RxOk { s with rx := .header ⟨.empty⟩ } :=
                rxOkOfRx fun _ _ _ hp => by cases hp
              exact ih hstep (rxOkRecvHeader hs1 rfl h01 h1) hr
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, -⟩ := hr
          exact rxOkOfRx fun _ _ _ hp => by cases hp
      · -- Inside a payload.
        next id remaining deliver fin hrx =>
        have hsz : (b.extract pos (pos + min remaining (b.size - pos))).size ≤
            min remaining (b.size - pos) := by
          simp only [ByteArray.size_extract]
          omega
        have hs1 := (stepsRecvChunk s id (b.extract pos (pos + min remaining (b.size - pos)))
          deliver).inv hs
        split at hr
        · -- The payload ends: the cursor goes back between frames.
          have hs2 := (stepsFinishPayload _ id deliver fin).inv hs1
          have hs3 := (Steps.rx _ (.header ⟨.empty⟩)).inv hs2
          exact ih hs3 (rxOkOfRx fun _ _ _ hp => by cases hp) hr
        ·
          have hs2 := (Steps.rx _ (.payload id (remaining - min remaining (b.size - pos))
            deliver fin)).inv hs1
          exact ih hs2 (rxOkChunk hrx h0 hsz (Nat.min_le_left _ _)) hr

private theorem rxOkSchedule {s : State} (a : Array Action) (h : RxOk s) : RxOk (schedule s a).1 := by
  unfold schedule
  dsimp only
  split
  · exact h
  · split <;> exact rxOkOfFields rfl rfl rfl rfl h

/-- Every step keeps the agreement of the cursor and the table. -/
theorem rxOkStep {s s' : State} {ev : Event} {acts : List Action} (hs : Inv s) (h0 : RxOk s)
    (hr : step s ev = .ok (s', acts)) : RxOk s' := by
  cases ev with
  | bytes p =>
    simp only [step] at hr
    cases hb : recvBytes (p.bytes.size + 1) (heard s p) p.bytes 0 #[] with
    | error e => simp [hb, Except.map] at hr
    | ok r =>
      obtain ⟨s1, a1⟩ := r
      simp only [hb, Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      -- `heard` and `schedule` change the timers alone.
      have hh : RxOk (heard s p) := by
        unfold heard; split
        · exact h0
        · exact rxOkOfFields rfl rfl rfl rfl h0
      exact rxOkSchedule a1 (rxOkRecvBytes _ ((stepsHeard s p).inv hs) hh hb)
  | tick t =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have ht : RxOk (onTick s t).1 := by
      unfold onTick sendPing
      dsimp only
      split
      · split
        · exact rxOkOfFields rfl rfl rfl rfl h0
        · exact rxOkOfFields rfl rfl rfl rfl h0
      · exact rxOkOfFields rfl rfl rfl rfl h0
    exact rxOkSchedule _ ht
  | eof =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact h0
  | openStream tag =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact rxOkOnOpen s tag h0
  | write k tag p =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact rxOkOnEntry (fun e rem hc => chargedWrite e tag p rem hc) h0
  | consumed k n =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact rxOkOnEntry (fun e rem hc => chargedConsume e n rem hc) h0
  | close k =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact rxOkOnEntry (fun e rem hc => chargedCloseLocal e rem hc) h0
  | reset k =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact rxOkOnEntry (fun e rem _ => chargedResetLocal e rem) h0
  | ping tag =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact rxOkSchedule _ (rxOkOfFields rfl rfl rfl rfl h0)
  | goAway =>
    simp only [step, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    unfold onGoAway
    split
    · exact h0
    · exact rxOkOfFields rfl rfl rfl rfl h0

/-- Every reachable state agrees with its cursor. So every chunk of a
payload that goes to a reading stream fits beside the bytes the reader
holds, and `offer` keeps it whole (`offerKeeps`): the core never drops
a byte it charged. -/
theorem Reachable.rxOk {r : Role} {s : State} (h : Reachable r s) : RxOk s := by
  induction h with
  | new => exact rxOkOfRx fun _ _ _ hp => by cases hp
  | step hreach hstep ih => exact rxOkStep hreach.inv ih hstep

end Yamux
