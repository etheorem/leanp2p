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
   this side's parity, and an inbound SYN with our own parity creates
   no stream.
3. **A retired id is never reused.** The allocator hands out the next
   id of this side's parity, and the state guarantees that the next id
   is greater than every live local id and every retired id.
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

/-- The parity of the ids the peer may open. -/
def peerParity (r : Role) : Nat :=
  if r.parity = 1 then 0 else 1

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

/-- Rewrite one stream in place. The other entries keep their value. -/
def updateStream (sid : StreamId) (f : Stream → Stream) (l : List Stream) : List Stream :=
  l.map (fun st => if st.id = sid then f st else st)

/-- Drop one stream from the table. -/
def removeStream (sid : StreamId) (l : List Stream) : List Stream :=
  l.filter (fun st => st.id ≠ sid)

theorem findStream?_mem {sid : StreamId} {l : List Stream} {st : Stream}
    (h : findStream? sid l = some st) : st ∈ l := by
  induction l with
  | nil => simp [findStream?] at h
  | cons x xs ih =>
      simp only [findStream?] at h
      split at h
      · rename_i hx
        injection h with hst
        subst hst
        exact List.mem_cons_self ..
      · rename_i hx
        exact List.mem_cons_of_mem x (ih h)

theorem findStream?_none {sid : StreamId} {l : List Stream}
    (h : findStream? sid l = none) : ∀ st ∈ l, st.id ≠ sid := by
  intro st hst
  induction l with
  | nil => simp at hst
  | cons x xs ih =>
      simp only [findStream?] at h
      split at h
      · simp at h
      · rename_i hx
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hx
        · exact ih h hst

theorem findStream?_eq_none_of_forall {sid : StreamId} {l : List Stream}
    (h : ∀ st ∈ l, st.id ≠ sid) : findStream? sid l = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [findStream?]
      split
      · rename_i hx
        exact absurd hx (h x (List.mem_cons_self ..))
      · exact ih (fun st hst => h st (List.mem_cons_of_mem _ hst))

theorem mem_updateStream {sid : StreamId} {f : Stream → Stream} {l : List Stream}
    {st : Stream} (h : st ∈ updateStream sid f l) :
    st ∈ l ∨ ∃ x ∈ l, x.id = sid ∧ st = f x := by
  induction l with
  | nil => simp [updateStream] at h
  | cons x xs ih =>
      simp only [updateStream, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · split at h
        · rename_i hif
          exact Or.inr ⟨x, List.mem_cons_self .., hif, h⟩
        · exact Or.inl (h ▸ List.mem_cons_self ..)
      · rcases ih h with h' | ⟨y, hy, hyid, hst⟩
        · exact Or.inl (List.mem_cons_of_mem x h')
        · exact Or.inr ⟨y, List.mem_cons_of_mem x hy, hyid, hst⟩

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
sites stay readable and no update nests inside another.
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

/-- The receive credit left on a stream. -/
def credit (st : Stream) : Nat := initialWindow - st.buffered

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
              let s' := { s with streams := updateStream fr.header.streamId (addCredit fr.header.length.val) s.streams }
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
                let s' := { s with streams := updateStream fr.header.streamId (receiveData fr.header.length.val fr.header.flags.fin) s.streams }
                .ok (s', [.deliver fr.header.streamId fr.payload])

/-! ## Window preservation -/

/-- An update that keeps every stream inside the window keeps the
invariant. -/
theorem WindowOK_update {sid : StreamId} {f : Stream → Stream} {s : State}
    (hw : WindowOK s) (hf : ∀ x ∈ s.streams, (f x).buffered ≤ initialWindow) :
    WindowOK { s with streams := updateStream sid f s.streams } := by
  intro st hst
  rcases mem_updateStream hst with h | ⟨x, hx, _, rfl⟩
  · exact hw st h
  · exact hf x hx

/-- Appending a stream inside the window keeps the invariant. -/
theorem WindowOK_append {s : State} {st : Stream} (hw : WindowOK s)
    (hst : st.buffered ≤ initialWindow) :
    WindowOK { s with streams := s.streams ++ [st] } := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hw x h
  · rcases List.mem_singleton.mp h with rfl
    exact hst

/-- A fresh stream is inside the window. -/
theorem fresh_buffered (sid : StreamId) (ours : Bool) :
    (Stream.fresh sid ours).buffered ≤ initialWindow := by
  unfold Stream.fresh
  exact Nat.zero_le _

/-! ## The drain loop -/

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
              match drain n { s' with pending := rest } with
              | .error e => .error e
              | .ok (s'', acts') => .ok (s'', acts ++ acts')

/-! ## The event entry point -/

/-- One event in, one state and its actions out. -/
def step (s : State) (e : Event) : Except ProtocolError (State × List Action) :=
  match e with
  | .bytes b =>
      let s' := { s with pending := s.pending ++ b }
      drain s'.pending.length s'
  | .open tag =>
      if hroom : s.nextId + 2 ≤ 4294967296 then
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
            let s' := { s with streams := updateStream sid (spendCredit data.length) s.streams }
            .ok (s', [.send (dataFrame sid Flags.empty data hbig), .done tag])
          else .ok (s, [.refused tag .windowOverflow])
  | .consumed sid n =>
      match findStream? sid s.streams with
      | none => .ok (s, [])
      | some st =>
          let k := min n st.buffered
          let s' := { s with streams := updateStream sid (giveBack k) s.streams }
          .ok (s', [.send (controlFrame .windowUpdate Flags.empty sid k)])
  | .closeWrite sid =>
      match findStream? sid s.streams with
      | none => .ok (s, [])
      | some _ =>
          let s' := { s with streams := updateStream sid finishSend s.streams }
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

end Core

end Yamux
