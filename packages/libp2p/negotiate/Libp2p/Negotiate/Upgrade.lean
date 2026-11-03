import Libp2p.Negotiate.Step
import Libp2p.Negotiate.Message
import Libp2p.Negotiate.Mock.Core
import Libp2p.Negotiate.Mock.Streams
import Libp2p.Negotiate.Mock.Identity
import Conc
import Bytes

/-!
# The upgrader

`Upgrade` walks a raw `Connection` through security negotiation, the
security handshake, the identity check, and muxer negotiation into a
`MuxSession` (root §4.9, negotiate ARCHITECTURE, "Public surface"). The
pure part is `drive`: one fuel-bounded run over a byte cursor that
feeds the 1a core one `Event.bytes` call per complete frame. The IO
part is `negotiate`, one negotiation stage, and `upgradeWith`, the
three-stage pipeline under one `Conc.withinDeadline`.

The driver owns the byte cursor. It never reads `s.buffer`; it resets
the buffer before every `step` call, and every unconsumed byte stays
in the `input` argument. The `leftover` field of the result is
authoritative. The shell always passes the
driver's own states and leftovers back, so the convention is closed
under use.

The negotiation loop parks on the connection read until a selection,
an error, a close, or the deadline (root §3.3). No measure bounds that
wait, so the loop keeps the package's `repeat` form, the form of
`Conc.TaskSet.joinAll`, and stays outside the proved core. The pure
`drive` is total, and its theorems carry no IO obligation.

The three stages thread the leftover bytes by contract 5 of the
package docs: the negotiation leftover seeds the handshake, the
`SecureConn` leftover seeds the muxer negotiation, and the muxer
negotiation leftover reaches `Muxer.open`.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate

open Bytes (DecodeError)

/-! ## The driver -/

/-- The answer of one driver run.

* `selected p consumed leftover writes`: a `step` selected `p`.
  `consumed` is the concatenation of the encoded frames the run
  consumed, the selected frame included. `leftover` is the byte suffix
  after it. `writes` are the `Action.write` payloads, in order.
* `waiting s consumed leftover writes`: `decodeMsg?` reported
  `truncated` on `leftover`. The caller reads more bytes and appends
  them; it must not call `drive` again without new bytes.
* `running s consumed leftover writes`: the fuel ran out after a
  complete frame. The caller calls `drive` again with `leftover`; it
  must not read. -/
inductive DriveResult where
  | selected (p : Mock.Core.ProtocolId) (consumed leftover : List Nat)
      (writes : List (List Nat))
  | waiting (s : State) (consumed leftover : List Nat) (writes : List (List Nat))
  | running (s : State) (consumed leftover : List Nat) (writes : List (List Nat))
  deriving Repr, DecidableEq

namespace DriveResult

/-- The frames the run consumed, as their encoded bytes. -/
@[simp] def consumed : DriveResult → List Nat
  | .selected _ c _ _ => c
  | .waiting _ c _ _ => c
  | .running _ c _ _ => c

/-- The bytes the run did not consume. -/
@[simp] def leftover : DriveResult → List Nat
  | .selected _ _ l _ => l
  | .waiting _ _ l _ => l
  | .running _ _ l _ => l

end DriveResult

/-- The `Action.write` payloads of an action list, in order. -/
def writesOf (actions : List Action) : List (List Nat) :=
  actions.filterMap fun
    | .write bs => some bs
    | .select .. => none

/-- The protocol an action list selects, if it selects one. -/
def selectOf : List Action → Option Mock.Core.ProtocolId
  | [] => none
  | .write _ :: rest => selectOf rest
  | .select p _ :: _ => some p

/-- One fuel unit consumes at most one complete frame. The
accumulators keep the consumed bytes and the writes of the run. -/
private def driveAux : Nat → State → List Nat → List Nat → List (List Nat) →
    Except Error DriveResult
  | 0, s, input, consumed, writes => .ok (.running s consumed input writes)
  | fuel + 1, s, input, consumed, writes =>
    match decodeMsg? input with
    | .error .truncated => .ok (.waiting s consumed input writes)
    | .error .malformed => .error (.decode .malformed)
    | .ok (m, rest) =>
      match step { s with buffer := [] } (.bytes input) with
      | .error e => .error e
      | .ok (s', actions) =>
        match selectOf actions with
        | some p =>
          .ok (.selected p (consumed ++ encodeMsg m) rest
            (writes ++ writesOf actions))
        | none =>
          driveAux fuel s' rest (consumed ++ encodeMsg m)
            (writes ++ writesOf actions)

/-- Drive the pure core over a byte cursor. `s.buffer` is
unused: pass every unconsumed byte in `input`, and read the
`leftover` field of the result as authoritative. One fuel unit
consumes at most one frame. -/
def drive (fuel : Nat) (s : State) (input : List Nat) : Except Error DriveResult :=
  driveAux fuel s input [] []

/-- The initiator's post-propose state and its one coalesced write.
The write holds the header and the first proposal back-to-back, the
lazy dialer's wire shape (contract 4 of the package docs). The state
carries the whole ordered list, so the core's `na` retry walks it.
An empty ordered list is a protocol error before any byte moves. -/
def initiatorStart (ids : List Mock.Core.ProtocolId) :
    Except Error (State × List (List Nat)) :=
  match ids with
  | [] => .error .negotiationFailed
  | p :: _ =>
    if ids.any (fun q => !fitsText q.toString) then .error .negotiationFailed
    else
      .ok ({ role := .initiator, supported := [], proposals := ids, buffer := [],
             phase := .negotiating },
           [encodeMsg header ++ encodeText p.toString])

/-- The responder's start: validate the offered list, then send the header
at once. The spec lets either side send first, and the responder that waits
for the dialer's header stalls a dialer that also waits. The state starts in
`negotiating` because the header is already on the wire. -/
def responderStart (ids : List Mock.Core.ProtocolId) :
    Except Error (State × List (List Nat)) :=
  if ids.any (fun q => !fitsText q.toString) then .error .negotiationFailed
  else if maxMsg < (lsBody ids).length then .error .negotiationFailed
  else
    .ok ({ role := .responder, supported := ids, proposals := [], buffer := [],
           phase := .negotiating },
         [encodeMsg header])

/-! ## The error mappings -/

/-- The rendered form of a decode error. `Bytes.DecodeError` carries no
`ToString` instance, so the mapping renders it here. -/
def renderDecodeError : Bytes.DecodeError → String
  | .truncated => "truncated"
  | .malformed => "malformed"

/-- Contract 8's one mapping point: every negotiation error becomes
the `protocol` arm, with the detail rendered. -/
def mapNegotiateError : Error → Mock.Core.Error
  | .decode e => .protocol ("multistream decode: " ++ renderDecodeError e)
  | .negotiationFailed => .protocol "multistream negotiation failed"

/-- The identity gate. `none` is the listen path, which accepts any
peer. The dial path compares the derived id against the expectation
and answers `authentication` on a difference, before any muxer byte
moves (negotiate ARCHITECTURE, "Decisions"). -/
def checkIdentity (expected : Option Mock.Identity.PeerId)
    (remote : Mock.Identity.PeerId) : Except Mock.Core.Error Unit :=
  match expected with
  | none => .ok ()
  | some e =>
    if e = remote then .ok ()
    else .error (.authentication "remote peer id differs from the expected peer id")

/-- The race answer flattened. `Conc.withinDeadline` constructs
`.error .deadlineExpired`; the `.closed` arm is required by the match
and is unreachable from `withinDeadline`. -/
def settleUpgrade {α : Type} :
    Except Conc.Error (Except Mock.Core.Error α) → Except Mock.Core.Error α
  | .ok (.ok a) => .ok a
  | .ok (.error e) => .error e
  | .error .deadlineExpired => .error (.timeout "upgrade deadline expired")
  | .error .closed => .error (.closed "upgrade deadline select closed")

/-- The answer of one negotiation stage: the selected id and the bytes
the stage over-read. `ByteArray` carries no `Repr` in Lean 4.34, so
the structure derives none; the suite prints the fields it needs. -/
structure StageResult where
  proto : Mock.Core.ProtocolId
  leftover : ByteArray

/-! ## The driver theorems -/

/-- The accumulator invariant behind the conservation law: the bytes
fed in equal the bytes consumed plus the final leftover, for every
arm of the result. The proof is the one induction of the unit, on the
fuel; `decodeMsgEncodeDecode` reassociates each consumed frame. -/
private theorem driveAux_conservation (fuel : Nat) :
    ∀ (s : State) (input consumed : List Nat) (writes : List (List Nat))
      (r : DriveResult),
      driveAux fuel s input consumed writes = .ok r →
      consumed ++ input = r.consumed ++ r.leftover := by
  induction fuel with
  | zero =>
    intro s input consumed writes r h
    simp only [driveAux, Except.ok.injEq] at h
    subst h
    simp
  | succ fuel ih =>
    intro s input consumed writes r h
    simp only [driveAux] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      simp
    · simp at h
    · rename_i m rest hdec
      split at h
      · rename_i e
        simp at h
      · rename_i s' actions hstep
        split at h
        · rename_i p
          simp only [Except.ok.injEq] at h
          subst h
          have hbs := decodeMsgEncodeDecode input m rest hdec
          rw [← hbs]
          simp [List.append_assoc]
        · have hrec := ih s' rest (consumed ++ encodeMsg m)
            (writes ++ writesOf actions) r h
          have hbs := decodeMsgEncodeDecode input m rest hdec
          rw [← hbs, ← List.append_assoc]
          exact hrec

/-- Every byte fed to the driver is consumed or left over. -/
theorem driveConservation {fuel : Nat} {s : State} {input : List Nat} {r : DriveResult}
    (h : drive fuel s input = .ok r) : input = r.consumed ++ r.leftover := by
  have h' := driveAux_conservation fuel s input [] [] r h
  simpa using h'

/-- The selected arm: the bytes in equal the frames consumed plus
the leftover handed to the next stage (contract 5). -/
theorem driveSelectedConservation {fuel : Nat} {s : State} {input : List Nat}
    {p : Mock.Core.ProtocolId} {consumed leftover : List Nat}
    {writes : List (List Nat)}
    (h : drive fuel s input = .ok (.selected p consumed leftover writes)) :
    input = consumed ++ leftover := by
  simpa using driveConservation h

/-- The truncated arm: every byte the run saw sits in the
consumed frames or in the waiting buffer, so the shell loses no byte
when it reads the next chunk. -/
theorem driveWaitingConservation {fuel : Nat} {s s' : State} {input : List Nat}
    {consumed leftover : List Nat} {writes : List (List Nat)}
    (h : drive fuel s input = .ok (.waiting s' consumed leftover writes)) :
    input = consumed ++ leftover := by
  simpa using driveConservation h

/-- The accumulator prefix invariant: a run appends the frames it
consumes to the accumulator it received. -/
private theorem driveAux_consumed_prefix (fuel : Nat) :
    ∀ (s : State) (input consumed : List Nat) (writes : List (List Nat))
      (r : DriveResult),
      driveAux fuel s input consumed writes = .ok r →
      ∃ tail : List Nat, r.consumed = consumed ++ tail := by
  induction fuel with
  | zero =>
    intro s input consumed writes r h
    simp only [driveAux, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp⟩
  | succ fuel ih =>
    intro s input consumed writes r h
    simp only [driveAux] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact ⟨[], by simp⟩
    · simp at h
    · rename_i m rest hdec
      split at h
      · rename_i e
        simp at h
      · rename_i s' actions hstep
        split at h
        · rename_i p
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨encodeMsg m, rfl⟩
        · obtain ⟨tail, htail⟩ :=
            ih s' rest (consumed ++ encodeMsg m) (writes ++ writesOf actions) r h
          exact ⟨encodeMsg m ++ tail, by rw [htail, List.append_assoc]⟩

/-- A frame the shell writes through `encodeMsg` decodes and appears
at the head of the consumed bytes. -/
theorem driveConsumedHead {fuel : Nat} {s : State} {m : Msg} {rest : List Nat}
    {r : DriveResult}
    (h : drive (fuel + 1) s (encodeMsg m ++ rest) = .ok r) :
    ∃ tail : List Nat, r.consumed = encodeMsg m ++ tail := by
  have h' : driveAux (fuel + 1) s (encodeMsg m ++ rest) [] [] = .ok r := h
  simp only [driveAux, encodeMsg, decodeMsgSuffix] at h'
  split at h'
  · rename_i e
    simp at h'
  · rename_i s' actions hstep
    split at h'
    · rename_i p
      simp only [Except.ok.injEq] at h'
      subst h'
      exact ⟨[], by simp [encodeMsg]⟩
    · obtain ⟨tail, htail⟩ :=
        driveAux_consumed_prefix fuel s' rest ([] ++ encodeMsg m) (writesOf actions) r h'
      exact ⟨tail, by simpa [encodeMsg, List.append_assoc] using htail⟩

/-- Two stages compose: bytes in equal the consumed bytes of both
stages plus the final leftover. The reusable form of the pipeline's scope
item 2. -/
theorem handoverCompose {ε α β : Type}
    {f : List Nat → Except ε (α × List Nat)}
    {g : List Nat → Except ε (β × List Nat)}
    {c₁ : α → List Nat} {c₂ : β → List Nat}
    {bs₁ bs₂ l₁ l₂ : List Nat} {a₁ : α} {a₂ : β}
    (law₁ : ∀ x a r, f x = .ok (a, r) → x = c₁ a ++ r)
    (law₂ : ∀ x a r, g x = .ok (a, r) → x = c₂ a ++ r)
    (h₁ : f bs₁ = .ok (a₁, l₁))
    (h₂ : g (l₁ ++ bs₂) = .ok (a₂, l₂)) :
    bs₁ ++ bs₂ = c₁ a₁ ++ c₂ a₂ ++ l₂ := by
  rw [law₁ bs₁ a₁ l₁ h₁, List.append_assoc, law₂ (l₁ ++ bs₂) a₂ l₂ h₂]
  simp only [List.append_assoc]

/-- The pure form of the hand-over: the muxer stage is seeded with
the negotiation's leftover, and the two drives consume exactly the
bytes fed in. -/
theorem driveTwostage {fuel₁ fuel₂ : Nat} {s₁ s₂ : State}
    {input₁ input₂ : List Nat} {p₁ p₂ : Mock.Core.ProtocolId}
    {c₁ c₂ l₁ l₂ : List Nat} {w₁ w₂ : List (List Nat)}
    (h₁ : drive fuel₁ s₁ input₁ = .ok (.selected p₁ c₁ l₁ w₁))
    (h₂ : drive fuel₂ s₂ (l₁ ++ input₂) = .ok (.selected p₂ c₂ l₂ w₂)) :
    input₁ ++ input₂ = c₁ ++ c₂ ++ l₂ := by
  have h1 := driveSelectedConservation h₁
  have h2 := driveSelectedConservation h₂
  rw [h1, List.append_assoc, h2]
  simp only [List.append_assoc]

/-- The shell's manual first write equals the core's propose
step for a singleton list, after both sides are read as write lists.
The driver therefore starts the negotiation the way the proved core
would. -/
theorem initiatorStartPropose {p : Mock.Core.ProtocolId}
    (hfits : fitsText p.toString = true) :
    initiatorStart [p] =
      (step { role := .initiator, supported := [], proposals := [], buffer := [],
              phase := .headerPending } (.propose p)).map
        (fun sa => (sa.1, writesOf sa.2)) := by
  have hany : ([p].any (fun q => !fitsText q.toString)) = false := by
    simp [List.any, hfits]
  simp only [initiatorStart, hany]
  rfl

/-- An empty ordered list is a protocol error before any byte is
written. -/
theorem initiatorStartNil : initiatorStart [] = .error .negotiationFailed := rfl

/-- The one mapping point of contract 8: every `Negotiate.Error`
becomes the `protocol` arm, with the detail rendered. -/
theorem mapNegotiateErrorSpec {e : Bytes.DecodeError} :
    mapNegotiateError (.decode e) =
      .protocol ("multistream decode: " ++ renderDecodeError e) ∧
    mapNegotiateError .negotiationFailed =
      .protocol "multistream negotiation failed" := by
  simp [mapNegotiateError]

/-- A differing derived id is authentication, before any muxer
byte moves. -/
theorem checkIdentityReject {expected remote : Mock.Identity.PeerId}
    (h : expected ≠ remote) :
    checkIdentity (some expected) remote =
      .error (.authentication "remote peer id differs from the expected peer id") := by
  simp [checkIdentity, h]

/-- The dial to the expected peer passes. -/
theorem checkIdentityAccept {e : Mock.Identity.PeerId} :
    checkIdentity (some e) e = .ok () := by
  simp [checkIdentity]

/-- The listen path accepts any peer. -/
theorem checkIdentityNone {r : Mock.Identity.PeerId} :
    checkIdentity none r = .ok () := rfl

/-- The deadline wiring of contract 6: the race's expiry is the
`timeout` arm, and the seam errors pass through untouched. The
`.closed` arm is required by the match over `Conc.Error`. -/
theorem settleUpgradeSpec {α : Type} {e : Mock.Core.Error} {a : α} :
    settleUpgrade (α := α) (.error .deadlineExpired) =
      .error (.timeout "upgrade deadline expired") ∧
    settleUpgrade (α := α) (.error .closed) =
      .error (.closed "upgrade deadline select closed") ∧
    settleUpgrade (α := α) (.ok (.error e)) = .error e ∧
    settleUpgrade (.ok (.ok a)) = .ok a := by
  simp [settleUpgrade]

/-! ## The IO shell -/

/-- Write each frame payload through the connection, in order. A
failed write is the `closed` arm: the connection is gone. -/
private def sendWrites (conn : Mock.Streams.Connection) (ws : List (List Nat)) :
    ExceptT Mock.Core.Error Conc.Async Unit := do
  for w in ws do
    match ← conn.write (Bytes.ofNatList w) with
    | .ok () => pure ()
    | .error _ => throw (.closed "connection write failed during the upgrade")

/-- The negotiation loop. It parks on `reader.read` only when `drive`
reports `waiting`; a `running` answer costs no read, because a
complete frame is still buffered. The loop ends on a selection, an
error, a close, or the deadline, so no measure bounds it (root §3.3).
The `repeat` form keeps the definition free of a `partial` marker,
like `Conc.TaskSet.joinAll`. -/
private def negotiateLoop (reader : Mock.Streams.BufReader)
    (conn : Mock.Streams.Connection) (s : State) (input : List Nat) :
    ExceptT Mock.Core.Error Conc.Async StageResult := do
  let mut s := s
  let mut input := input
  repeat
    match drive 1 s input with
    | .error e => throw (mapNegotiateError e)
    | .ok (.selected p _ leftover writes) => do
        sendWrites conn writes
        return { proto := p, leftover := Bytes.ofNatList leftover }
    | .ok (.waiting s' _ leftover writes) => do
        sendWrites conn writes
        match ← reader.read with
        | none => throw (.closed "multistream negotiation ended before a selection")
        | some chunk =>
            s := s'
            input := leftover ++ Bytes.toNatList chunk
    | .ok (.running s' _ leftover writes) => do
        sendWrites conn writes
        s := s'
        input := leftover
  -- Every arm above returns or loops, so the `repeat` never falls
  -- through. The tail keeps the loop total without an `Inhabited`.
  throw (.closed "the negotiation loop ended without an answer")

/-- One negotiation stage. The initiator writes the coalesced header
plus first proposal before the loop; the responder reads first. The
seed is the leftover of the previous stage. The end of the stream
mid-negotiation is `Core.Error.closed`; a `Negotiate.Error` maps once
through `mapNegotiateError`. -/
def negotiate (role : Mock.Core.Role) (reader : Mock.Streams.BufReader)
    (conn : Mock.Streams.Connection) (seed : ByteArray)
    (ids : List Mock.Core.ProtocolId) :
    ExceptT Mock.Core.Error Conc.Async StageResult := do
  match role with
  | .initiator =>
    match initiatorStart ids with
    | .error e => throw (mapNegotiateError e)
    | .ok (s, first) => do
        sendWrites conn first
        negotiateLoop reader conn s (Bytes.toNatList seed)
  | .responder =>
    match responderStart ids with
    | .error e => throw (mapNegotiateError e)
    | .ok (s, first) => do
        sendWrites conn first
        negotiateLoop reader conn s (Bytes.toNatList seed)

/-- The pipeline: negotiate the security protocol, run the handshake,
check the identity, negotiate the muxer, open the session. Each lookup
is total; a miss after a selection is `protocol`. -/
private def upgradeCore (role : Mock.Core.Role) (conn : Mock.Streams.Connection)
    (leftover : ByteArray) (expected : Option Mock.Identity.PeerId)
    (secs : List Mock.Core.SecurityProtocol) (muxers : List Mock.Core.Muxer) :
    Conc.Async (Except Mock.Core.Error (Mock.Core.MuxSession × Mock.Identity.PeerId)) := do
  let reader := Mock.Streams.BufReader.ofConn conn
  match ← negotiate role reader conn leftover (secs.map (·.id)) with
  | .error e => return .error e
  | .ok stage =>
    match secs.find? (fun s => decide (s.id = stage.proto)) with
    | none => return .error (.protocol "selected security protocol is not configured")
    | some sec =>
      match ← sec.handshake role conn stage.leftover with
      | .error e => return .error e
      | .ok sc =>
        match checkIdentity expected sc.remotePeer with
        | .error e => return .error e
        | .ok () =>
          let muxReader := Mock.Streams.BufReader.ofConn sc.conn
          match ← negotiate role muxReader sc.conn sc.leftover (muxers.map (·.id)) with
          | .error e => return .error e
          | .ok stage2 =>
            match muxers.find? (fun m => decide (m.id = stage2.proto)) with
            | none => return .error (.protocol "selected muxer is not configured")
            | some mux =>
              match ← mux.«open» role sc.conn stage2.leftover with
              | .error e => return .error e
              | .ok session => return .ok (session, sc.remotePeer)

/-- Whether the deadline boundary already closed the connection. Both error
arms of `withinDeadline` run the expiry hook. -/
private def boundaryClosed {α : Type} : Except Conc.Error α → Bool
  | .error _ => true
  | .ok _ => false

/-- Give a late session back to its owner. A result that arrives after the
timer won never reaches a caller, so the release closes it here. -/
private def releaseLate (r : Except Mock.Core.Error
    (Mock.Core.MuxSession × Mock.Identity.PeerId)) : BaseIO Unit :=
  match r with
  | .ok pair => pair.1.close
  | .error _ => pure ()

/-- The upgrade under one `Conc.withinDeadline`. The expiry closes
the connection once at the boundary (root §3.5), and the race's
`deadlineExpired` maps to the `timeout` arm through `settleUpgrade`.
The clock is a seam, so the deadline test can advance it. -/


def upgradeWith (clock : Conc.Clock) (role : Mock.Core.Role)
    (conn : Mock.Streams.Connection) (leftover : ByteArray)
    (expected : Option Mock.Identity.PeerId)
    (secs : List Mock.Core.SecurityProtocol) (muxers : List Mock.Core.Muxer) :
    ExceptT Mock.Core.Error Conc.Async (Mock.Core.MuxSession × Mock.Identity.PeerId) := do
  let answer ← Conc.withinDeadline clock Mock.Streams.upgradeDeadlineMs conn.close
    (upgradeCore role conn leftover expected secs muxers)
    releaseLate
  match settleUpgrade answer with
  | .ok pair => return pair
  | .error e => do
      -- Both error arms of the boundary run the expiry hook, which closed the
      -- connection once. Only a failure inside the work leaves it open.
      if boundaryClosed answer then throw e
      else do
        conn.close
        throw e

/-- The frozen entry of the package docs. The clock is fixed to the
system clock here and stays a seam in `upgradeWith` for the deadline
test. -/
def upgrade (role : Mock.Core.Role) (conn : Mock.Streams.Connection)
    (leftover : ByteArray) (expected : Option Mock.Identity.PeerId)
    (secs : List Mock.Core.SecurityProtocol) (muxers : List Mock.Core.Muxer) :
    ExceptT Mock.Core.Error Conc.Async (Mock.Core.MuxSession × Mock.Identity.PeerId) :=
  upgradeWith Conc.Clock.system role conn leftover expected secs muxers

end Libp2p.Negotiate
