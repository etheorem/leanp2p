import Bytes
import Yamux.Constants
import Yamux.Error
import Yamux.Frame
import Yamux.Header

/-!
# Yamux core

The pure state machine of a yamux session (ARCHITECTURE §3.3). `step`
takes one event and returns the next state and the actions to perform.
It reads no clock, holds no `IO.Ref`, and spawns no task, so a test can
drive it with a captured transcript and the kernel can prove its
invariants.

The invariants this module states and proves:

1. **The receive window never overruns.** A stream's buffered bytes
   never exceed the window we granted it, and a data frame that would
   overrun is a protocol error rather than a promise to allocate.
2. **Ids keep their parity.** A stream this side opens always carries
   this side's parity, and the state guarantees that the next id stays
   greater than every live local id and every retired id.
3. **A retired id is never reused.** The allocator hands out the next
   id of this side's parity, and retirement only ever records ids the
   list already holds.

The loop that drives this core and the session that serves `Stream`
values live in the modules above (ARCHITECTURE §3.3).
-/

namespace Yamux

/-- Which side of the session this endpoint is. The client opens odd
stream ids and the server even ones (the yamux specification). -/
inductive Role where
  | client
  | server
  deriving Repr, DecidableEq, BEq, Hashable

namespace Role

/-- The parity of the ids this side may open. -/
def parity : Role → Nat
  | .client => 1
  | .server => 0

end Role

/-- One live stream. -/
structure Stream where
  /-- The stream id. -/
  id : StreamId
  /-- This side opened it. The name avoids the `local` keyword. -/
  ours : Bool
  /-- Bytes received from the peer that the application has not consumed
  yet. The window we granted minus this number is the credit the peer
  still has. -/
  buffered : Nat
  /-- Credit the peer granted us, in bytes. -/
  sendWindow : Nat
  /-- Our write direction is finished. -/
  sendClosed : Bool
  /-- The peer's write direction is finished. -/
  recvClosed : Bool
  deriving Repr, DecidableEq, BEq, Hashable

namespace Stream

/-- A fresh stream with the full initial window on both sides. -/
def fresh (id : StreamId) (ours : Bool) : Stream :=
  { id := id, ours := ours, buffered := 0, sendWindow := initialWindow,
    sendClosed := false, recvClosed := false }

end Stream

/-- The session state. -/
structure State where
  /-- This endpoint's role. -/
  role : Role
  /-- The live streams, in creation order. -/
  streams : List Stream
  /-- The next id this side may hand out. It keeps this side's parity. -/
  nextId : Nat
  /-- Ids that must never be handed out again. -/
  retired : List Nat
  /-- Bytes read off the connection that do not form a frame yet. -/
  pending : List Nat
  /-- The peer ended the session, or we did. -/
  closing : Bool
  deriving Repr, DecidableEq, BEq, Hashable

/-- Events into the core. -/
inductive Event where
  /-- Bytes arrived off the connection, including plaintext the muxer
  negotiation over-read. -/
  | bytes (b : List Nat)
  /-- The application asks for a new stream. -/
  | open (tag : Nat)
  /-- The application writes to a stream. -/
  | write (sid : StreamId) (tag : Nat) (data : List Nat)
  /-- The application consumed bytes, which returns credit to the peer. -/
  | consumed (sid : StreamId) (n : Nat)
  /-- The application half-closes its write direction. -/
  | closeWrite (sid : StreamId)
  /-- The application aborts both directions. -/
  | reset (sid : StreamId)
  /-- A timer tick. Time is an input, never a read. -/
  | tick (now : Nat)
  deriving Repr, DecidableEq, BEq

/-- Actions the shell performs. -/
inductive Action where
  /-- Write these bytes to the connection: exactly one frame. -/
  | send (bytes : List Nat)
  /-- Hand these bytes to the application on a stream. -/
  | deliver (sid : StreamId) (data : List Nat)
  /-- The peer opened a stream; hand it to the application. -/
  | accept (sid : StreamId)
  /-- The stream the application asked for exists. -/
  | opened (tag : Nat) (sid : StreamId)
  /-- The tagged write reached the wire. -/
  | done (tag : Nat)
  /-- The tagged write cannot go. -/
  | refused (tag : Nat) (e : ProtocolError)
  /-- Tear the connection down. -/
  | close
  deriving Repr, DecidableEq, BEq

namespace Core

/-! ## The stream table -/

/-- The live stream with this id, if it exists. -/
def findStream? (sid : StreamId) : List Stream → Option Stream
  | [] => none
  | st :: rest => if st.id = sid then some st else findStream? sid rest

/-- The stream a lookup found carries the id the lookup asked for. -/
theorem findStream?_id {sid : StreamId} {l : List Stream} {st : Stream}
    (h : findStream? sid l = some st) : st.id = sid := by
  induction l with
  | nil => simp [findStream?] at h
  | cons x xs ih =>
      simp only [findStream?] at h
      split at h
      · rename_i hx
        injection h with hst
        subst hst
        exact hx
      · exact ih h

/-- Replace every entry with this id by the given stream. The table stays
a list, so a stream counts once per matching entry, which is what the
window bound needs. -/
def replaceStream (sid : StreamId) (st : Stream) (l : List Stream) : List Stream :=
  l.map (fun x => if x.id = sid then st else x)

/-- Every entry of a replaced table is the replacement or was already
there. -/
theorem mem_replaceStream {sid : StreamId} {st : Stream} {l : List Stream}
    {x : Stream} (h : x ∈ replaceStream sid st l) : x = st ∨ x ∈ l := by
  induction l with
  | nil => simp [replaceStream] at h
  | cons y ys ih =>
      simp only [replaceStream, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · split at h
        · exact Or.inl h
        · exact Or.inr (h ▸ List.mem_cons_self ..)
      · rcases ih h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem y h')

/-- Drop one stream from the table. -/
def removeStream (sid : StreamId) (l : List Stream) : List Stream :=
  l.filter (fun st => st.id ≠ sid)

/-- A stream a lookup found is in the table. -/
theorem findStream?_mem {sid : StreamId} {l : List Stream} {st : Stream}
    (h : findStream? sid l = some st) : st ∈ l := by
  induction l with
  | nil => simp [findStream?] at h
  | cons x xs ih =>
      simp only [findStream?] at h
      split at h
      · injection h with hst
        subst hst
        exact List.mem_cons_self ..
      · rename_i hx
        exact List.mem_cons_of_mem x (ih h)

/-! ## The invariants -/

/-- No stream holds more buffered bytes than the window it granted. -/
def WindowOK (s : State) : Prop :=
  ∀ st ∈ s.streams, st.buffered ≤ initialWindow

/-- The allocating side keeps its parity, stays inside the id field, and
never hands out an id that is live or retired. -/
def IdsOK (s : State) : Prop :=
  s.nextId % 2 = s.role.parity ∧
  s.nextId + 2 ≤ 4294967296 ∧
  (∀ st ∈ s.streams, st.ours = true → st.id.val < s.nextId) ∧
  (∀ r ∈ s.retired, r < s.nextId)

/-- Every invariant at once. -/
def Inv (s : State) : Prop := WindowOK s ∧ IdsOK s

/-! ## Stream updates

Named functions keep every record update in one place, so the call
sites stay readable and no update nests inside another. Each one keeps
the id and the ownership bit, which the id invariant needs.
-/

/-- Add credit the peer granted. -/
def addCredit (delta : Nat) (x : Stream) : Stream :=
  { x with sendWindow := x.sendWindow + delta }

/-- Spend credit on a write. -/
def spendCredit (n : Nat) (x : Stream) : Stream :=
  { x with sendWindow := x.sendWindow - n }

/-- Return credit after the application consumed bytes. -/
def giveBack (n : Nat) (x : Stream) : Stream :=
  { x with buffered := x.buffered - n }

/-- Record received data and, when the frame carried `FIN`, the end of
the peer's write direction. -/
def receiveData (len : Nat) (fin : Bool) (x : Stream) : Stream :=
  { x with buffered := x.buffered + len, recvClosed := x.recvClosed || fin }

/-- Mark our write direction finished. -/
def finishSend (x : Stream) : Stream :=
  { x with sendClosed := true }

/-! ## Frame encoding helpers -/

/-- A control frame: the value rides in the header's length field and the
payload is empty. -/
def controlFrame (t : FrameType) (fl : Flags) (sid : StreamId) (value : Nat) : List Nat :=
  Header.encode (Header.ofParts t fl sid (Word32.ofNat value)) ++ []

/-- A data frame with the given payload. -/
def dataFrame (sid : StreamId) (fl : Flags) (payload : List Nat)
    (h : payload.length < 4294967296) : List Nat :=
  Header.encode (Header.ofParts .data fl sid ⟨payload.length, h⟩) ++ payload

/-! ## Applying one frame -/

/-- Apply one complete frame. -/
def apply (s : State) (fr : Frame) : Except ProtocolError (State × List Action) :=
  if s.closing then .error .sessionClosed
  else
    match fr.header.frameType with
    | .goAway =>
        let s' := { s with closing := true }
        .ok (s', [.close])
    | .ping =>
        if fr.header.streamId.val = 0 then
          .ok (s, [.send (controlFrame .ping ⟨false, true, false, false⟩
            fr.header.streamId fr.header.length.val)])
        else .error .unknownStream
    | .windowUpdate =>
        match findStream? fr.header.streamId s.streams with
        | some st =>
            if st.sendWindow + fr.header.length.val > maxWindow then .error .windowOverflow
            else
              let st' := addCredit fr.header.length.val st
              let s' := { s with streams := replaceStream fr.header.streamId st' s.streams }
              .ok (s', [])
        | none =>
            if fr.header.flags.syn then
              if fr.header.streamId.val % 2 = s.role.parity then .ok (s, [])
              else
                let s' := { s with streams :=
                  s.streams ++ [Stream.fresh fr.header.streamId false] }
                .ok (s', [.send (controlFrame .windowUpdate ⟨false, true, false, false⟩
                  fr.header.streamId 0), .accept fr.header.streamId])
            else .ok (s, [])
    | .data =>
        if fr.header.streamId.val = 0 then .error .unknownStream
        else
          match findStream? fr.header.streamId s.streams with
          | none => .ok (s, [])
          | some st =>
              if st.buffered + fr.header.length.val > initialWindow then .error .overlongData
              else
                let st' := receiveData fr.header.length.val fr.header.flags.fin st
                let s' := { s with streams := replaceStream fr.header.streamId st' s.streams }
                .ok (s', [.deliver fr.header.streamId fr.payload])

/-! ## Window preservation -/

/-- Replacing an in-window stream keeps the invariant. -/
theorem WindowOK_replace {sid : StreamId} {st : Stream} {s : State}
    (hw : WindowOK s) (hst : st.buffered ≤ initialWindow) :
    WindowOK { s with streams := replaceStream sid st s.streams } := by
  intro x hx
  rcases mem_replaceStream hx with rfl | hx
  · exact hst
  · exact hw x hx

/-- Appending an in-window stream keeps the invariant. -/
theorem WindowOK_append {s : State} {st : Stream} (hw : WindowOK s)
    (hst : st.buffered ≤ initialWindow) :
    WindowOK { s with streams := s.streams ++ [st] } := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hw x h
  · rcases List.mem_singleton.mp h with rfl
    exact hst

/-- A fresh stream starts at zero, so it is inside any window. -/
theorem fresh_buffered (sid : StreamId) (ours : Bool) :
    (Stream.fresh sid ours).buffered ≤ initialWindow := by
  unfold Stream.fresh
  exact Nat.zero_le _

/-- A frame the core accepts leaves every stream inside the window
(ARCHITECTURE §4.8, contract 1). -/
theorem apply_WindowOK {s : State} {fr : Frame} {s' : State} {acts : List Action}
    (hw : WindowOK s) (h : apply s fr = .ok (s', acts)) : WindowOK s' := by
  unfold apply at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp only [Except.ok.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hw
    · split at h
      · simp only [Except.ok.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hw
      · simp at h
    · split at h
      · rename_i st hfind
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          obtain ⟨rfl, _⟩ := h
          apply WindowOK_replace hw
          show st.buffered ≤ initialWindow
          exact hw st (findStream?_mem hfind)
      · split at h
        · split at h
          · simp only [Except.ok.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact hw
          · simp only [Except.ok.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact WindowOK_append hw (fresh_buffered _ _)
        · simp only [Except.ok.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact hw
    · split at h
      · simp at h
      · split at h
        · simp only [Except.ok.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact hw
        · rename_i st hfind
          split at h
          · simp at h
          · rename_i hcred
            simp only [Except.ok.injEq] at h
            obtain ⟨rfl, _⟩ := h
            apply WindowOK_replace hw
            show st.buffered + fr.header.length.val ≤ initialWindow
            have h1 := hcred
            unfold initialWindow at h1 ⊢
            omega

/-! ## Id preservation -/

/-- Replacing an entry keeps the id invariant: the replacement carries
the id and the ownership bit of the entry it replaces. -/
theorem IdsOK_replace {sid : StreamId} {st st' : Stream} {s : State}
    (hi : IdsOK s) (hid : st'.id = st.id) (hours : st'.ours = st.ours)
    (hfind : st ∈ s.streams) :
    IdsOK { s with streams := replaceStream sid st' s.streams } := by
  refine ⟨hi.1, hi.2.1, ?_, hi.2.2.2⟩
  intro x hx hxours
  rcases mem_replaceStream hx with hxst | hx
  · rw [hxst] at hxours ⊢
    rw [hid] at ⊢
    have h' : st.ours = true := by
      rw [← hours]
      exact hxours
    exact hi.2.2.1 st hfind h'
  · exact hi.2.2.1 x hx hxours

/-- Appending a peer-opened stream keeps the id invariant: its ownership
bit is false, so the local-id bound does not apply to it. -/
theorem IdsOK_append_remote {s : State} {st : Stream} (hi : IdsOK s)
    (hremote : st.ours = false) :
    IdsOK { s with streams := s.streams ++ [st] } := by
  refine ⟨hi.1, hi.2.1, ?_, hi.2.2.2⟩
  intro x hx hxours
  rcases List.mem_append.mp hx with h | h
  · exact hi.2.2.1 x h hxours
  · rcases List.mem_singleton.mp h with rfl
    rw [hremote] at hxours
    exact absurd hxours (by decide)

/-- A frame the core accepts keeps the id invariant. -/
theorem apply_IdsOK {s : State} {fr : Frame} {s' : State} {acts : List Action}
    (hi : IdsOK s) (h : apply s fr = .ok (s', acts)) : IdsOK s' := by
  unfold apply at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp only [Except.ok.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hi
    · split at h
      · simp only [Except.ok.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hi
      · simp at h
    · split at h
      · rename_i st hfind
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact IdsOK_replace (st := st) hi rfl rfl (findStream?_mem hfind)
      · split at h
        · split at h
          · simp only [Except.ok.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact hi
          · simp only [Except.ok.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact IdsOK_append_remote hi rfl
        · simp only [Except.ok.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact hi
    · split at h
      · simp at h
      · split at h
        · simp only [Except.ok.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact hi
        · rename_i st hfind
          split at h
          · simp at h
          · simp only [Except.ok.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact IdsOK_replace (st := st) hi rfl rfl (findStream?_mem hfind)

/-! ## The drain loop -/

/-- Move the loop to the bytes that follow the frame it just applied. -/
def advance (s : State) (rest : List Nat) : State :=
  { s with pending := rest }

/-- Apply every complete frame in the pending buffer. `fuel` bounds the
number of steps; the caller passes the buffer length, which suffices
because every frame consumes at least its twelve header bytes. -/
def drain : Nat → State → Except ProtocolError (State × List Action)
  | 0, s => .ok (s, [])
  | n + 1, s =>
      match Frame.parse? s.pending with
      | .error e => .error e
      | .ok none => .ok (s, [])
      | .ok (some (fr, rest)) =>
          match apply s fr with
          | .error e => .error e
          | .ok (s', acts) =>
              match drain n (advance s' rest) with
              | .error e => .error e
              | .ok (s'', acts') => .ok (s'', acts ++ acts')

/-- The drain loop keeps every invariant: each frame it applies keeps
them, and the pending buffer is not part of any invariant. -/
theorem drain_Inv : ∀ (n : Nat) (s : State), Inv s →
    ∀ s' acts, drain n s = .ok (s', acts) → Inv s' := by
  intro n
  induction n with
  | zero =>
      intro s hi s' acts h
      simp only [drain, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hi
  | succ k ih =>
      intro s hi s' acts h
      simp only [drain] at h
      cases hp : Frame.parse? s.pending with
      | error e => simp [hp] at h
      | ok r =>
          cases r with
          | none =>
              simp [hp] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hi
          | some fr_rest =>
              obtain ⟨fr, rest⟩ := fr_rest
              cases ha : apply s fr with
              | error e => simp [hp, ha] at h
              | ok pair =>
                  obtain ⟨s1, acts1⟩ := pair
                  cases hd : drain k (advance s1 rest) with
                  | error e => simp [hp, ha, hd] at h
                  | ok pair2 =>
                      obtain ⟨s2, acts2⟩ := pair2
                      simp [hp, ha, hd] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hw1 : WindowOK (advance s1 rest) := by
                        unfold advance
                        exact apply_WindowOK (s' := s1) hi.1 ha
                      have hid1 : IdsOK (advance s1 rest) := by
                        unfold advance
                        exact apply_IdsOK (s' := s1) hi.2 ha
                      exact ih (advance s1 rest) ⟨hw1, hid1⟩ _ _ hd

/-! ## The event entry point -/

/-- One event in, one state and its actions out. -/
def step (s : State) (e : Event) : Except ProtocolError (State × List Action) :=
  match e with
  | .bytes b =>
      let s' := { s with pending := s.pending ++ b }
      drain s'.pending.length s'
  | .open tag =>
      if hroom : s.nextId + 4 ≤ 4294967296 then
        let sid : StreamId := ⟨s.nextId, by omega⟩
        let s1 := { s with streams := s.streams ++ [Stream.fresh sid true] }
        let s2 := { s1 with nextId := s.nextId + 2 }
        .ok (s2, [.send (controlFrame .windowUpdate ⟨true, false, false, false⟩ sid 0),
          .opened tag sid])
      else .error .exhausted
  | .write sid tag data =>
      match findStream? sid s.streams with
      | none => .ok (s, [.refused tag .unknownStream])
      | some st =>
          if st.sendClosed then .ok (s, [.refused tag .unknownStream])
          else if data.length > st.sendWindow then
            .ok (s, [.refused tag .windowOverflow])
          else if data.length > maxDataFrame then
            .ok (s, [.refused tag .windowOverflow])
          else if hbig : data.length < 4294967296 then
            let st' := spendCredit data.length st
            let s' := { s with streams := replaceStream sid st' s.streams }
            .ok (s', [.send (dataFrame sid Flags.empty data hbig), .done tag])
          else .ok (s, [.refused tag .windowOverflow])
  | .consumed sid n =>
      match findStream? sid s.streams with
      | none => .ok (s, [])
      | some st =>
          let k := min n st.buffered
          let st' := giveBack k st
          let s' := { s with streams := replaceStream sid st' s.streams }
          .ok (s', [.send (controlFrame .windowUpdate Flags.empty sid k)])
  | .closeWrite sid =>
      match findStream? sid s.streams with
      | none => .ok (s, [])
      | some st =>
          let st' := finishSend st
          let s' := { s with streams := replaceStream sid st' s.streams }
          .ok (s', [.send (dataFrame sid ⟨false, false, true, false⟩ [] (by decide))])
  | .reset sid =>
      match findStream? sid s.streams with
      | none => .ok (s, [])
      | some st =>
          let s1 := { s with streams := removeStream sid s.streams }
          let s2 := { s1 with retired :=
            if st.ours then st.id.val :: s.retired else s.retired }
          .ok (s2, [.send (controlFrame .data ⟨false, false, false, true⟩ sid 0)])
  | .tick _ => .ok (s, [])

/-- Removing a stream keeps the window invariant. -/
theorem WindowOK_remove {sid : StreamId} {s : State} (hw : WindowOK s) :
    WindowOK { s with streams := removeStream sid s.streams } := by
  intro x hx
  exact hw x (List.mem_filter.mp hx).1

/-- The event entry point keeps every invariant. -/
theorem step_Inv {s : State} {e : Event} {s' : State} {acts : List Action}
    (hi : Inv s) (h : step s e = .ok (s', acts)) : Inv s' := by
  cases e with
  | bytes b =>
      unfold step at h
      dsimp only at h
      exact drain_Inv (s.pending ++ b).length { s with pending := s.pending ++ b } hi s' acts h
  | «open» tag =>
      unfold step at h
      dsimp only at h
      split at h
      · rename_i hroom
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hw : WindowOK { s with streams := s.streams ++ [Stream.fresh ⟨s.nextId, by omega⟩ true] } :=
          WindowOK_append hi.1 (fresh_buffered _ _)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact hw
        · show (s.nextId + 2) % 2 = s.role.parity
          rw [show (s.nextId + 2) % 2 = s.nextId % 2 from by
            rw [show s.nextId + 2 = s.nextId + 2 * 1 from by omega]
            exact Nat.add_mul_mod_self_left ..]
          exact hi.2.1
        · show s.nextId + 2 + 2 ≤ 4294967296
          omega
        · intro x hx hxours
          rcases List.mem_append.mp hx with hx | hx
          · have hlt := hi.2.2.2.1 x hx hxours
            show x.id.val < s.nextId + 2
            omega
          · rcases List.mem_singleton.mp hx with rfl
            show s.nextId < s.nextId + 2
            omega
        · intro r hr
          have hlt := hi.2.2.2.2 r hr
          show r < s.nextId + 2
          omega
      · simp at h
  | write sid tag data =>
      unfold step at h
      dsimp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hi
      · rename_i st hfind
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hi
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hi
          · split at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hi
            · split at h
              · rename_i hbig
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hmem := findStream?_mem hfind
                refine ⟨?_, ?_⟩
                · exact WindowOK_replace hi.1 (by show st.buffered ≤ initialWindow; exact hi.1 st hmem)
                · exact IdsOK_replace (st := st) hi.2 rfl rfl hmem
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact hi
  | consumed sid n =>
      unfold step at h
      dsimp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hi
      · rename_i st hfind
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem := findStream?_mem hfind
        refine ⟨?_, ?_⟩
        · apply WindowOK_replace hi.1
          show st.buffered - min n st.buffered ≤ initialWindow
          have := hi.1 st hmem
          omega
        · exact IdsOK_replace (st := st) hi.2 rfl rfl hmem
  | closeWrite sid =>
      unfold step at h
      dsimp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hi
      · rename_i st hfind
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem := findStream?_mem hfind
        refine ⟨?_, ?_⟩
        · exact WindowOK_replace hi.1 (by show st.buffered ≤ initialWindow; exact hi.1 st hmem)
        · exact IdsOK_replace (st := st) hi.2 rfl rfl hmem
  | reset sid =>
      unfold step at h
      dsimp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hi
      · rename_i st hfind
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem := findStream?_mem hfind
        refine ⟨WindowOK_remove hi.1, ?_⟩
        refine ⟨hi.2.1, hi.2.2.1, ?_, ?_⟩
        · intro x hx hxours
          exact hi.2.2.2.1 x (List.mem_filter.mp hx).1 hxours
        · intro r hr
          by_cases hh : st.ours = true
          · simp [hh] at hr ⊢
            rcases hr with hr' | hr
            · rw [hr']
              exact hi.2.2.2.1 st hmem hh
            · exact hi.2.2.2.2 r hr
          · simp [hh] at hr ⊢
            exact hi.2.2.2.2 r hr
  | tick now =>
      unfold step at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hi

/-- A stream this side opens carries this side's parity, and the id was
never retired. This is the observable form of the id invariant: the
parity rule and the no-reuse rule reach the application through the
`opened` action. -/
theorem open_parity {s : State} {s' : State} {tag : Nat} {acts : List Action}
    (hi : Inv s) (h : step s (.open tag) = .ok (s', acts)) :
    ∃ sid : StreamId, Action.opened tag sid ∈ acts ∧ sid.val % 2 = s.role.parity ∧
      (∀ r ∈ s.retired, r ≠ sid.val) := by
  unfold step at h
  dsimp only at h
  split at h
  · rename_i hroom
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨⟨s.nextId, by omega⟩, ?_, hi.2.1, ?_⟩
    · simp
    · intro r hr hEq
      have hlt := hi.2.2.2.2 r hr
      have hEq' : r = s.nextId := hEq
      omega
  · simp at h

end Core

end Yamux
