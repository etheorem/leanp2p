import Tests.Support
import Conc
import Libp2p.Core
import Std.Data.HashMap

/-!
# Core interface tests

Compile-time checks cover instances and interface construction.
Runtime checks cover error rendering, registry lookup, session shutdown,
and per-connection stream limits. Dependency mocks expose no
constructors, so examples requiring their values take them as arguments.
-/

set_option autoImplicit false

namespace Tests.Libp2pCore

open Libp2p Libp2p.Core Libp2p.Core.Mock
open Conc

/-! ## The derived classes (§3.2, §3.4) -/

example : DecidableEq Role := inferInstance
example : Hashable Role := inferInstance
example : Repr Role := inferInstance

example : DecidableEq ProtocolId := inferInstance
example : Hashable ProtocolId := inferInstance
example : Ord ProtocolId := inferInstance
example : Repr ProtocolId := inferInstance
example : ToString ProtocolId := inferInstance
-- `Std.HashMap` needs a lawful `==`. `DecidableEq` gives the only `BEq`
-- instance on the type, and that instance is lawful.
example : LawfulBEq ProtocolId := inferInstance

example : DecidableEq Core.Error := inferInstance
example : Hashable Core.Error := inferInstance
example : Repr Core.Error := inferInstance
example : DecidableEq Decision := inferInstance

#guard Role.initiator != Role.responder
#guard Role.initiator.opposite == Role.responder
#guard Role.responder.opposite == Role.initiator
#guard Decision.allow != Decision.deny

/-! ## `ProtocolId` -/

private def echoId : ProtocolId := ⟨"/test/echo/1.0.0"⟩

private def toySecurityId : ProtocolId := ⟨"/test/toy-security/1.0.0"⟩

private def toyMuxId : ProtocolId := ⟨"/test/toy-mux/1.0.0"⟩

-- Equality compares the strings byte for byte, as libp2p routes by
-- exact literal match.
#guard echoId == (⟨"/test/echo/1.0.0"⟩ : ProtocolId)
#guard echoId != (⟨"/test/echo/1.0.1"⟩ : ProtocolId)
#guard echoId != (⟨"/test/echo/1.0.0/"⟩ : ProtocolId)
#guard toString echoId == "/test/echo/1.0.0"
#guard compare (⟨"/a"⟩ : ProtocolId) ⟨"/b"⟩ == .lt

#guard echoId != toyMuxId

example (a b : ProtocolId) (h : a.toString = b.toString) : a = b :=
  (ProtocolId.eq_iff_toString_eq a b).mpr h

/-! ## `Core.Error` -/

private def allErrors : List Core.Error :=
  [.protocol "bad frame", .authentication "wrong key", .timeout "30000 ms", .closed "eof"]

#guard allErrors.map Core.Error.detail == ["bad frame", "wrong key", "30000 ms", "eof"]
#guard allErrors.map Core.Error.render ==
  ["protocol error: bad frame", "authentication failed: wrong key",
   "timeout: 30000 ms", "closed: eof"]
#guard allErrors.map toString == allErrors.map Core.Error.render

private inductive ToyError where
  | badFrame
  deriving Repr

private instance : ToString ToyError := ⟨fun | .badFrame => "bad frame"⟩

private def toyStep (ok : Bool) : Except ToyError Nat :=
  if ok then .ok 1 else .error .badFrame

-- Mapping a protocol error preserves its rendered detail.
#guard
  match (toyStep false).mapError Core.Error.ofProtocol with
  | .error e => e == .protocol "bad frame"
  | .ok _ => false
#guard
  match (toyStep true).mapError Core.Error.ofProtocol with
  | .ok n => n == 1
  | .error _ => false

-- An IO shell maps the same way with `ExceptT.adapt`.
example (shell : ExceptT ToyError Async Nat) : ExceptT Core.Error Async Nat :=
  ExceptT.adapt Core.Error.ofProtocol shell

private def failure? {α : Type} : Except Core.Error α → Option Core.Error
  | .error e => some e
  | .ok _ => none

private def isClosedArm {α : Type} (x : Except Core.Error α) : Bool :=
  match failure? x with
  | some (.closed _) => true
  | _ => false

private def isProtocolArm {α : Type} (x : Except Core.Error α) : Bool :=
  match failure? x with
  | some (.protocol _) => true
  | _ => false

private def isOrderly (x : Except Core.Error Unit) : Bool :=
  (failure? x).isNone

private def errorChecks (r : Runner) : IO Unit := do
  for e in allErrors do
    r.check s!"{repr e} renders its detail" ((toString e).endsWith e.detail)
  -- One detail under each arm: the log line still tells the arms apart.
  let same : List Core.Error := [.protocol "x", .authentication "x", .timeout "x", .closed "x"]
  r.check "the four arms render four different lines for one detail"
    ((same.map toString).eraseDups.length == 4)

/-! ## The security seam -/

/-- A handshake double that preserves the connection and negotiation
leftovers, with the supplied peer ids. -/
private def toySecurity (localPeer remotePeer : Identity.PeerId) : SecurityProtocol where
  id := toySecurityId
  handshake := fun _role conn negotiated =>
    pure { conn, localPeer, remotePeer, leftover := negotiated, join := pure (.ok ()) }

example (p q : Identity.PeerId) : (toySecurity p q).id = toySecurityId := rfl

example (p q : Identity.PeerId) : Option SecurityProtocol :=
  [toySecurity p q].find? (·.id == toySecurityId)

-- Wait for the tasks before reading the session outcome.
example (conn : Streams.Connection) (p q : Identity.PeerId) (ts : TaskSet)
    (o : Outcome Core.Error) : SecureConn :=
  { conn, localPeer := p, remotePeer := q, leftover := .empty
    join := do
      ts.joinAll
      o.answer }

example (m : Muxer) (sc : SecureConn) (rest : ByteArray) :
    ExceptT Core.Error Async MuxSession :=
  m.open .initiator sc.conn (sc.leftover ++ rest)

/-! ## The muxer seam -/

/-- A session double with an empty accept queue. Closing ends pending
accepts and releases `join`. -/
private def toySession : BaseIO MuxSession := do
  let incoming : Chan Streams.Stream ← Chan.new 4
  let done : Chan Unit ← Chan.new 1
  return {
    openStream := fun _protocol => do
      -- The ascription marks the read `BaseIO`, so the lift into
      -- `ExceptT Core.Error Async` applies (see `Conc.TaskSet.joinAll`).
      if (← (done.isClosed : BaseIO Bool)) then
        throwThe Core.Error (.closed "the toy session has ended")
      else
        throwThe Core.Error (.protocol "the toy session opens no streams")
    accept := incoming.recv
    close := do
      incoming.close
      done.close
    join := do
      -- `done` never carries a value, so the receive ends at the close.
      let _ ← done.recv
      return .ok ()
  }

private def toyMuxer : Muxer where
  id := toyMuxId
  -- `open` is a keyword, so the field name takes guillemets here.
  «open» := fun _role _conn _negotiated => do
    let s ← (toySession : BaseIO MuxSession)
    return s

example : toyMuxer.id = toyMuxId := rfl

private def sessionChecks (r : Runner) : Async Unit := do
  let s ← (toySession : BaseIO MuxSession)
  r.check "a live toy session refuses openStream as a protocol error"
    (isProtocolArm (← (s.openStream echoId).run))
  let got : OnceRef (Option Bool) ← OnceRef.new none
  let ts ← TaskSet.new
  ts.spawn do
    let next ← s.accept
    got.set (some next.isNone)
  -- Nothing ever enters the accept queue, so the task can only answer
  -- through the close, whether it parks before the close or after it.
  s.close
  ts.joinAll
  r.check "close ends a pending accept with none" ((← got.get) == some true)
  r.check "join answers an orderly end after close" (isOrderly (← s.join))
  r.check "openStream after close answers closed" (isClosedArm (← (s.openStream echoId).run))
  s.close
  r.check "a second close changes nothing" (isOrderly (← s.join))

/-! ## The handler seam and the registry -/

private def echoHandler : StreamHandler where
  id := echoId
  handle := fun _stream => pure ()

private def registry : Std.HashMap ProtocolId StreamHandler :=
  Std.HashMap.ofList [(echoHandler.id, echoHandler)]

#guard (registry.get? ⟨"/test/echo/1.0.0"⟩).map (·.id) == some echoId
#guard (registry.get? ⟨"/test/echo/2.0.0"⟩).isNone

private def registryChecks (r : Runner) : IO Unit := do
  let proposed : ProtocolId := ⟨String.join ["/test/echo", "/1.0.0"]⟩
  r.check "a registry finds the handler by an equal id"
    ((registry.get? proposed).map (·.id) == some echoId)
  r.check "a registry misses an unknown id"
    (registry.get? toyMuxId).isNone

/-! ## The policy hooks -/

private def allowAll : ConnectionGater where
  allowDial := fun _ _ => pure .allow
  allowAccept := fun _ => pure .allow
  allowSecured := fun _ _ => pure .allow

private def denyInbound : ConnectionGater where
  allowDial := fun _ _ => pure .allow
  allowAccept := fun _ => pure .deny
  allowSecured := fun role _ =>
    pure (if role == .responder then .deny else .allow)

private def unlimitedScope : ResourceScope where
  reserveMemory := fun _ => pure .allow
  releaseMemory := fun _ => pure ()
  close := pure ()

private def unlimitedConnection : ConnectionScope where
  toResourceScope := unlimitedScope
  setPeer := fun _ => pure .allow
  openStream := fun _ => pure (some unlimitedScope)

private def unlimited : ResourceManager where
  openConnection := fun _ _ => pure (some unlimitedConnection)

-- Associate the authenticated peer before granting streams.
example (rm : ResourceManager) (addr : Multiformats.Multiaddr) (peer : Identity.PeerId) :
    BaseIO (Option ResourceScope) := do
  let some conn ← rm.openConnection .responder addr | return none
  if (← conn.setPeer peer) == .deny then
    conn.close
    return none
  conn.openStream .responder

/-- A connection scope that allows `limit` live streams. Each stream
scope gives its slot back once, on its first close. The counts change
through `OnceRef.updateGet`, one atomic step each (§4.1 rule 3). -/
private def limitedConnection (limit : Nat) : BaseIO ConnectionScope := do
  let live : OnceRef Nat ← OnceRef.new 0
  let openStream (_role : Role) : BaseIO (Option ResourceScope) := do
    let granted ← live.updateGet fun n => if n < limit then (true, n + 1) else (false, n)
    if !granted then return none
    let closed : OnceRef Bool ← OnceRef.new false
    return some {
      reserveMemory := fun _ => pure .allow
      releaseMemory := fun _ => pure ()
      close := do
        let first ← closed.updateGet fun c => (!c, true)
        if first then live.update (· - 1)
    }
  return { unlimitedScope with setPeer := fun _ => pure .allow, openStream }

/-- The stream counts belong to their connection. The limit is 2, so a
second close that freed a second slot would show: `Nat` subtraction
stops at 0, and a limit of 1 would hide it. -/
private def resourceChecks (r : Runner) : IO Unit := do
  let a ← limitedConnection 2
  let b ← limitedConnection 2
  let s1 ← a.openStream .initiator
  let s2 ← a.openStream .responder
  r.check "a connection grants streams within its limit" (s1.isSome && s2.isSome)
  r.check "the connection refuses a stream over its limit" (← a.openStream .initiator).isNone
  r.check "another connection counts its own streams" (← b.openStream .initiator).isSome
  if let some s := s1 then
    s.close
    s.close
  r.check "a closed stream frees a slot on its own connection" (← a.openStream .initiator).isSome
  r.check "a second close frees no second slot" (← a.openStream .initiator).isNone

private def keepOrder : AddressRanker where
  rank := fun _ addrs => addrs
  rank_perm := fun _ _ => by apply List.Perm.refl

private def reverseOrder : AddressRanker where
  rank := fun _ addrs => addrs.reverse
  rank_perm := fun _ _ => by apply List.reverse_perm

example (p : Identity.PeerId) (a b : Multiformats.Multiaddr) :
    reverseOrder.rank p [a, b] = [b, a] := rfl

example (p : Identity.PeerId) (addrs : List Multiformats.Multiaddr) :
    (keepOrder.rank p addrs).length = addrs.length :=
  keepOrder.length_rank p addrs

example : List ConnectionGater × ResourceManager := ([allowAll, denyInbound], unlimited)

/-- Run the core interface checks. -/
def run (r : Runner) : IO Unit := do
  r.section "libp2p core" "(packages/libp2p/core/docs/PLAN.md, test milestones)"
  errorChecks r
  registryChecks r
  resourceChecks r
  let all : Async Unit := sessionChecks r
  all.run

end Tests.Libp2pCore
