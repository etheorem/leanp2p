import Libp2p.Negotiate.Message
import Libp2p.Negotiate.Mock.Core
import Bytes

/-!
# The pure negotiation core

`State`, `Event`, `Action`, and `step` are the pure state machine of
multistream-select (root §3.3). One `Event.bytes` feeds raw bytes, and
the core decodes exactly one frame per call, so the
malformed-versus-incomplete call stays in the core (§3.1). A decoded
frame goes through a private `classify` step that names the verdict,
then a private `act` step that performs it. Every theorem about choice
lives in `classify`; every theorem about writes and phase lives in
`act`.

The step returns `Except Error (State × List Action)`, the root §3.3
shape. `Action.error` of the package docs stays out: the error channel
carries the failure (root §3.5), and no contract asks for an error
action.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate

open Bytes (DecodeError)

/-- The phase of one negotiation. -/
inductive Phase where
  | headerPending
  | negotiating
  | awaitingAnswer
  | selected
  deriving Repr, DecidableEq

/-- The core state. `role` is the side. `supported` is the responder's
ordered list. `proposals` is the initiator's remaining list, in order.
`buffer` holds the bytes no frame has consumed yet. -/
structure State where
  role : Mock.Core.Role
  supported : List Mock.Core.ProtocolId
  proposals : List Mock.Core.ProtocolId
  buffer : List Nat
  phase : Phase
  deriving Repr, DecidableEq

/-- One input to the core. Raw bytes arrive as one event; a proposal
is the local dialer's input. -/
inductive Event where
  | bytes (bs : List Nat)
  | propose (p : Mock.Core.ProtocolId)
  deriving Repr, DecidableEq

/-- One output of the core. A write carries framed bytes. A select
ends the negotiation with the chosen id and the leftover bytes. -/
inductive Action where
  | write (bs : List Nat)
  | select (proto : Mock.Core.ProtocolId) (leftover : List Nat)
  deriving Repr, DecidableEq

/-- The replies the responder sends, the closed set of §3.4. -/
inductive Reply where
  | na
  | ls
  deriving DecidableEq, Repr, Hashable

/-- The wire text of a reply. -/
def Reply.text : Reply → String
  | .na => "na"
  | .ls => "ls"

/-- The table the inverse searches. -/
def Reply.all : List Reply := [.na, .ls]

/-- The computed inverse of `Reply.text`: a text names a reply when it
equals the reply's text. -/
def Reply.ofText? (s : String) : Option Reply := Reply.all.find? (fun r => r.text = s)

/-- The table conformance: the inverse reads exactly the reply whose
text it is given. -/
theorem Reply.ofText?EqSome {s : String} {r : Reply} :
    Reply.ofText? s = some r ↔ r.text = s := by
  constructor
  · intro h
    have := List.find?_some h
    simpa using this
  · intro h
    subst h
    have hmem : r ∈ Reply.all := by cases r <;> simp [Reply.all]
    unfold Reply.ofText?
    cases r <;> simp [Reply.all, Reply.text]

/-- The reply as a message. The text is the message text. -/
def Reply.toMsg : Reply → Msg
  | .na => ⟨"na", by decide⟩
  | .ls => ⟨"ls", by decide⟩

/-- The message form of the reply recognition. -/
def Reply.ofMsg? (m : Msg) : Option Reply := Reply.ofText? m.text

/-- Why a negotiation failed. `decode` carries the shared decode
error; `negotiationFailed` covers every peer violation the core sees. -/
inductive Error where
  | decode (e : DecodeError)
  | negotiationFailed
  deriving Repr, DecidableEq

/-- The pure negotiation core of the spike: the first of `ours` that
`theirs` also supports. -/
def choose (ours theirs : List Mock.Core.ProtocolId) : Option Mock.Core.ProtocolId :=
  List.find? theirs.contains ours

/-- A chosen id is in our list and supported by theirs. -/
theorem choose_spec {ours theirs : List Mock.Core.ProtocolId} {p : Mock.Core.ProtocolId}
    (h : choose ours theirs = some p) : p ∈ ours ∧ theirs.contains p = true := by
  unfold choose at h
  exact ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-! ## The verdicts -/

/-- What a decoded text means for this state. Byte-free, so every
theorem about choice lives here. -/
private inductive Verdict where
  | echo
  | listIds
  | pick (p : Mock.Core.ProtocolId)
  | refuse
  | advance
  | retry (q : Mock.Core.ProtocolId) (ps : List Mock.Core.ProtocolId)
  | accept (p : Mock.Core.ProtocolId)
  | fail

/-- Classify a decoded text for a state. -/
private def classify (s : State) (text : String) : Verdict :=
  match s.role, s.phase with
  | .responder, .headerPending => if text = protocolId.toString then .echo else .fail
  | .responder, .negotiating =>
      match Reply.ofText? text with
      | some .ls => .listIds
      | _ =>
        if text = protocolId.toString then .advance
        else if (⟨text⟩ : Mock.Core.ProtocolId) ∈ s.supported then .pick ⟨text⟩
        else .refuse
  | .initiator, .negotiating => if text = protocolId.toString then .advance else .fail
  | .initiator, .awaitingAnswer =>
      match s.proposals with
      | [] => .fail
      | p :: ps =>
        if Reply.ofText? text = some .na then
          match ps with
          | [] => .fail
          | q :: qs => .retry q (q :: qs)
        else if text = p.toString then .accept p else .fail
  | _, _ => .fail

/-- Perform a verdict. Byte-free per verdict, so every theorem about
writes and phase lives here. -/
private def act (s : State) (rest : List Nat) : Verdict → Except Error (State × List Action)
  | .echo => .ok ({ s with buffer := rest, phase := .negotiating }, [.write (encodeText protocolId.toString)])
  | .listIds => .ok ({ s with buffer := rest }, [.write (encodeLs s.supported)])
  | .pick p => .ok ({ s with buffer := [], phase := .selected },
      [.write (encodeText p.toString), .select p rest])
  | .refuse => .ok ({ s with buffer := rest }, [.write (encodeMsg (Reply.toMsg .na))])
  | .advance =>
    match s.role with
    | .initiator => .ok ({ s with buffer := rest, phase := .awaitingAnswer }, [])
    | .responder => .ok ({ s with buffer := rest }, [])
  | .retry q ps => .ok ({ s with buffer := rest, proposals := ps }, [.write (encodeText q.toString)])
  | .accept p => .ok ({ s with buffer := [], phase := .selected }, [.select p rest])
  | .fail => .error .negotiationFailed

/-- A proposal event. An initiator in the header phase records the id in
`proposals` and writes the coalesced header plus the first proposal frame. A
second proposal in the same phase extends the list and writes nothing. The
frame for every later id is written when `step` answers `na`, and `classify`
derives that answer from the recorded list. -/
private def propose (s : State) (p : Mock.Core.ProtocolId) : Except Error (State × List Action) :=
  if s.role = .initiator then
    if s.phase = .headerPending then
      if s.proposals = [] then
        .ok ({ s with proposals := [p], phase := .negotiating },
             [.write (encodeMsg header ++ encodeText p.toString)])
      else .ok ({ s with proposals := s.proposals ++ [p] }, [])
    else .ok (s, [])
  else .ok (s, [])

/-- One transition of the core. A `bytes` event appends to the buffer
and decodes one frame. `truncated` keeps the buffer and waits;
`malformed` is a protocol error; a decoded frame goes through
`classify` and `act`. -/
def step (s : State) : Event → Except Error (State × List Action)
  | .propose p => propose s p
  | .bytes bs =>
      match decodeMsg? (s.buffer ++ bs) with
      | .error .truncated => .ok ({ s with buffer := s.buffer ++ bs }, [])
      | .error .malformed => .error (.decode .malformed)
      | .ok (m, rest) => act s rest (classify s m.text)

/-! ## The verdict lemmas -/

/-- A step that selects came from the pick or accept verdict. -/
private theorem actSelect {s : State} {rest : List Nat} {v : Verdict} {s' : State}
    {acts : List Action} {p : Mock.Core.ProtocolId} {r : List Nat}
    (h : act s rest v = .ok (s', acts)) (hm : Action.select p r ∈ acts) :
    v = .pick p ∨ v = .accept p := by
  cases v <;> simp only [act] at h
    <;> ((try split at h)
         <;> (try simp only [Except.ok.injEq, Prod.mk.injEq] at h)
         <;> (try obtain ⟨-, rfl⟩ := h)
         <;> (try simp_all))

/-- A pick comes from the responder's supported list. -/
private theorem classifyPick {s : State} {t : String} {p : Mock.Core.ProtocolId}
    (h : classify s t = .pick p) : p ∈ s.supported := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- An accept comes from the head of the initiator's proposals. -/
private theorem classifyAcceptInitiator {s : State} {t : String} {p : Mock.Core.ProtocolId}
    (h : classify s t = .accept p) : p ∈ s.proposals := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- An accept carries the accepted text. -/
private theorem classifyAcceptText {s : State} {t : String} {p : Mock.Core.ProtocolId}
    (h : classify s t = .accept p) : p.toString = t := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- A responder never accepts. -/
private theorem classifyAcceptResponder {s : State} {t : String} {p : Mock.Core.ProtocolId}
    (hr : s.role = .responder) (h : classify s t = .accept p) : False := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- An initiator never picks. -/
private theorem classifyPickInitiator {s : State} {t : String} {p : Mock.Core.ProtocolId}
    (hr : s.role = .initiator) (h : classify s t = .pick p) : False := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- An initiator never sees the echo verdict. -/
private theorem classifyEchoInitiator {s : State} {t : String}
    (hr : s.role = .initiator) (h : classify s t = .echo) : False := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- An initiator never sees the list verdict. -/
private theorem classifyListIdsInitiator {s : State} {t : String}
    (hr : s.role = .initiator) (h : classify s t = .listIds) : False := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- An initiator never sees the refuse verdict. -/
private theorem classifyRefuseInitiator {s : State} {t : String}
    (hr : s.role = .initiator) (h : classify s t = .refuse) : False := by
  unfold classify at h
  repeat' split at h
  all_goals simp_all

/-- The `ls` text in the negotiation draws the list verdict. -/
private theorem classifyListIds {s : State} {t : String}
    (hrole : s.role = .responder) (hphase : s.phase = .negotiating)
    (hls : Reply.ofText? t = some .ls) : classify s t = .listIds := by
  unfold classify
  rw [hrole, hphase]
  rw [hls]

/-- An unknown id in the negotiation draws the refuse verdict. -/
private theorem classifyRefuse {s : State} {t : String}
    (hrole : s.role = .responder) (hphase : s.phase = .negotiating)
    (hnot : (⟨t⟩ : Mock.Core.ProtocolId) ∉ s.supported)
    (hheader : t ≠ protocolId.toString) (hreply : Reply.ofText? t = none) :
    classify s t = .refuse := by
  unfold classify
  rw [hrole, hphase]
  simp only [hreply]
  rw [ite_eq_right hheader, ite_eq_right hnot]

/-- A retry pops one proposal: the new list is the tail of the old. -/
private theorem classifyRetryTail {s : State} {t : String} {q : Mock.Core.ProtocolId}
    {ps : List Mock.Core.ProtocolId} (h : classify s t = .retry q ps) :
    s.proposals.tail = ps := by
  unfold classify at h
  repeat' split at h
  all_goals (cases h <;> simp_all [List.tail_cons])

/-- A write came from one of the five writing verdicts. -/
private theorem actWriteVerdict {s : State} {rest : List Nat} {v : Verdict} {s' : State}
    {actions : List Action} {w : List Nat}
    (h : act s rest v = .ok (s', actions)) (hw : Action.write w ∈ actions) :
    v = .echo ∨ v = .listIds ∨ (∃ p, v = .pick p) ∨ v = .refuse ∨
      (∃ q ps, v = .retry q ps) := by
  cases v with
  | echo => exact Or.inl rfl
  | listIds => exact Or.inr (Or.inl rfl)
  | pick p => exact Or.inr (Or.inr (Or.inl ⟨p, rfl⟩))
  | refuse => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | retry q ps => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, ps, rfl⟩)))
  | advance =>
      simp only [act] at h
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      all_goals (obtain ⟨-, rfl⟩ := h; simp at hw)
  | accept p =>
      simp only [act] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp at hw
  | fail =>
      simp only [act] at h
      cases h

/-- The list verdict writes the `ls` reply and stays in the phase. -/
private theorem actListIds {s : State} {rest : List Nat} {s' : State} {actions : List Action}
    (h : act s rest .listIds = .ok (s', actions)) :
    actions = [.write (encodeLs s.supported)] ∧ s'.phase = s.phase ∧ s'.buffer = rest := by
  unfold act at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hstate, hact⟩ := h
  subst hact
  rw [← hstate]
  simp

/-- The refuse verdict writes the `na` frame and stays in the phase. -/
private theorem actRefuse {s : State} {rest : List Nat} {s' : State} {actions : List Action}
    (h : act s rest .refuse = .ok (s', actions)) :
    actions = [.write (encodeMsg (Reply.toMsg .na))] ∧ s'.phase = s.phase ∧ s'.buffer = rest := by
  unfold act at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hstate, hact⟩ := h
  subst hact
  rw [← hstate]
  simp

/-- The retry verdict replaces the proposals with the remaining list. -/
private theorem actRetryWrites {s : State} {rest : List Nat} {q : Mock.Core.ProtocolId}
    {ps : List Mock.Core.ProtocolId} {s' : State} {actions : List Action}
    (h : act s rest (.retry q ps) = .ok (s', actions)) : s'.proposals = ps := by
  unfold act at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hstate, _⟩ := h
  rw [← hstate]

/-! ## The step theorems -/

/-- A responder selects only from its supported list (contract 2). -/
theorem step_select_responder_mem {s : State} {bs : List Nat} {s' : State}
    {actions : List Action} {p : Mock.Core.ProtocolId} {rest : List Nat}
    (hrole : s.role = .responder)
    (hstep : step s (.bytes bs) = .ok (s', actions))
    (hmem : Action.select p rest ∈ actions) : p ∈ s.supported := by
  simp only [step] at hstep
  split at hstep
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨-, rfl⟩ := hstep
    simp at hmem
  · simp at hstep
  · rcases actSelect hstep hmem with hv | hv
    · exact classifyPick hv
    · exact (classifyAcceptResponder hrole hv).elim

/-- An initiator selects only from its own proposal list. -/
theorem step_select_initiator_mem {s : State} {bs : List Nat} {s' : State}
    {actions : List Action} {p : Mock.Core.ProtocolId} {rest : List Nat}
    (hrole : s.role = .initiator)
    (hstep : step s (.bytes bs) = .ok (s', actions))
    (hmem : Action.select p rest ∈ actions) : p ∈ s.proposals := by
  simp only [step] at hstep
  split at hstep
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨-, rfl⟩ := hstep
    simp at hmem
  · simp at hstep
  · rcases actSelect hstep hmem with hv | hv
    · exact (classifyPickInitiator hrole hv).elim
    · exact classifyAcceptInitiator hv

/-- A step that writes advances the initiator's proposal list by one
head: the new list is the old tail, so it is strictly shorter
(contract 2, the `na` retry). -/
theorem step_initiator_na_progress {s : State} {bs : List Nat} {s' : State}
    {actions : List Action} {p : Mock.Core.ProtocolId} {ps : List Mock.Core.ProtocolId}
    {w : List Nat}
    (hrole : s.role = .initiator) (hprop : s.proposals = p :: ps)
    (hstep : step s (.bytes bs) = .ok (s', actions))
    (hwrite : Action.write w ∈ actions) :
    s'.proposals = ps ∧ s'.proposals.length < s.proposals.length := by
  simp only [step] at hstep
  split at hstep
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
    obtain ⟨-, rfl⟩ := hstep
    simp at hwrite
  · simp at hstep
  · rcases actWriteVerdict hstep hwrite with hc | hc | hc | hc | hc
    · exact (classifyEchoInitiator hrole hc).elim
    · exact (classifyListIdsInitiator hrole hc).elim
    · rcases hc with ⟨p', hc⟩
      exact (classifyPickInitiator hrole hc).elim
    · exact (classifyRefuseInitiator hrole hc).elim
    · rcases hc with ⟨q, ps', hc⟩
      rw [hc] at hstep
      have hnew : s'.proposals = ps' := actRetryWrites hstep
      have htail : s.proposals.tail = ps' := classifyRetryTail hc
      have hps : ps' = ps := by
        rw [← htail, hprop]
        rfl
      constructor
      · rw [hnew, hps]
      · rw [hnew, hps, hprop]
        simp only [List.length_cons]
        omega

/-- The `ls` answer writes the reply and stays in the negotiation
(contract 3). -/
theorem step_responder_ls_stays {s : State} {bs : List Nat} {s' : State}
    {actions : List Action} {m : Msg} {rest : List Nat}
    (hrole : s.role = .responder) (hphase : s.phase = .negotiating)
    (hdec : decodeMsg? (s.buffer ++ bs) = .ok (m, rest))
    (hls : Reply.ofMsg? m = some .ls)
    (hstep : step s (.bytes bs) = .ok (s', actions)) :
    actions = [.write (encodeLs s.supported)] ∧ s'.phase = .negotiating ∧ s'.buffer = rest := by
  simp only [step, hdec] at hstep
  have hc := classifyListIds hrole hphase hls
  rw [hc] at hstep
  have ha := actListIds hstep
  rcases ha with ⟨hacts, hphase', hbuf⟩
  constructor
  · exact hacts
  constructor
  · rw [hphase']
    exact hphase
  · exact hbuf

/-- An unknown id draws the `na` frame and stays in the negotiation
(contract 2). -/
theorem step_responder_unknown_stays {s : State} {bs : List Nat} {s' : State}
    {actions : List Action} {m : Msg} {rest : List Nat} {id : Mock.Core.ProtocolId}
    (hrole : s.role = .responder) (hphase : s.phase = .negotiating)
    (hdec : decodeMsg? (s.buffer ++ bs) = .ok (m, rest))
    (htext : m.text = id.toString) (hnot : id ∉ s.supported)
    (hheader : m.text ≠ protocolId.toString)
    (hreply : Reply.ofMsg? m = none)
    (hstep : step s (.bytes bs) = .ok (s', actions)) :
    actions = [.write (encodeMsg (Reply.toMsg .na))] ∧ s'.phase = .negotiating ∧ s'.buffer = rest := by
  have hnot' : (⟨m.text⟩ : Mock.Core.ProtocolId) ∉ s.supported := by
    intro hm
    apply hnot
    simpa [htext] using hm
  simp only [step, hdec] at hstep
  have hc := classifyRefuse hrole hphase hnot' hheader hreply
  rw [hc] at hstep
  have ha := actRefuse hstep
  rcases ha with ⟨hacts, hphase', hbuf⟩
  constructor
  · exact hacts
  constructor
  · rw [hphase']
    exact hphase
  · exact hbuf

/-- Conservation: the bytes the accepting initiator consumed, plus the
leftover, equal the bytes fed in (contract 5). -/
theorem step_select_conservation {s : State} {bs : List Nat} {s' : State}
    {p : Mock.Core.ProtocolId} {rest r : List Nat} {m : Msg}
    (hrole : s.role = .initiator)
    (hdec : decodeMsg? (s.buffer ++ bs) = .ok (m, r))
    (hstep : step s (.bytes bs) = .ok (s', [Action.select p rest])) :
    s.buffer ++ bs = encodeText p.toString ++ rest := by
  simp only [step, hdec] at hstep
  have hmem : Action.select p rest ∈ [Action.select p rest] := by simp
  have hv := actSelect hstep hmem
  rcases hv with hc | hc
  · exact (classifyPickInitiator hrole hc).elim
  · have hpt : p.toString = m.text := classifyAcceptText hc
    rw [hc] at hstep
    have hr : r = rest := by
      unfold act at hstep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, hact⟩ := hstep
      injection hact with hsel hnil
      injection hsel with hp hrest
    have hlaw : encodeText m.text ++ r = s.buffer ++ bs :=
      decodeMsgEncodeDecode (s.buffer ++ bs) m r hdec
    rw [← hlaw]
    rw [← hpt]
    rw [hr]

/-- A truncated buffer waits: no actions, no error, the phase holds,
and the buffer keeps the bytes (§3.1). -/
theorem step_truncated_waits {s : State} {bs : List Nat} {s' : State} {actions : List Action}
    (hdec : decodeMsg? (s.buffer ++ bs) = .error .truncated)
    (hstep : step s (.bytes bs) = .ok (s', actions)) :
    actions = [] ∧ s'.phase = s.phase ∧ s'.buffer = s.buffer ++ bs := by
  simp only [step, hdec] at hstep
  simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
  obtain ⟨hstate, hact⟩ := hstep
  subst hact
  rw [← hstate]
  simp

end Libp2p.Negotiate
