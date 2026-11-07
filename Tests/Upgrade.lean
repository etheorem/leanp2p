import Tests.Support
import Libp2p.Negotiate
import Libp2p.Identity
import Conc
import Bytes
import Streams.Conn
import Streams.BufReader
import Streams.Stream
import Streams.Constants
import Streams.Sim
import Multiformats.Multiaddr

/-!
# The upgrade suite (unit 1b)

The test milestones of the negotiate package plan, unit 1b. The full
pipeline runs both directions over an in-process pipe pair, and the
byte-split runs use the in-memory sim transport of `Streams.Sim`. The
fixed-key plaintext security value and the minimal muxer value replace
the Noise and yamux milestones (#16, #17, unmerged). The deadline check
advances the test `Clock` of `base/conc`, so the suite waits on no wall
clock.

Every check that spawns a task joins it (PRINCIPLES 3.2), and every
park wakes by a close (PRINCIPLES 3.1). Shared cells change only by
`OnceRef` steps (ARCHITECTURE §4.1, rule 3).
-/

set_option autoImplicit false

namespace Tests.Upgrade

open Libp2p.Negotiate
open Conc
open Bytes (DecodeError)
open Lean (Json)

/-! ## The test seam values -/

/-- One direction of a pipe pair: the read side and the write side. -/
private structure Side where
  read : Conc.Pipe
  write : Conc.Pipe

/-- A multiaddr from its text form. -/
private def simAddr (text : String) : Async Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? text with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {text} does not parse"

/-- The connection view of a pipe pair. The streams seam reports a
failed write by throwing `IO.Error`, while `Conc.Pipe.write` reports
the same failure in its `Except` answer. -/
private def pipeConn (read write : Conc.Pipe) : Async Streams.Connection := do
  let addr ← simAddr "/memory/0"
  return { read := read.read
           write := fun b => do
             match ← write.write b with
             | .ok () => pure ()
             | .error _ => throw (IO.Error.resourceVanished 0 "test pipe closed")
           close := do
             read.close
             write.close
           localAddr := addr
           remoteAddr := addr }

/-- The connection view of one side. The close reaches both
directions, like a transport close. -/
private def sideConn (s : Side) : Async Streams.Connection :=
  pipeConn s.read s.write

/-- A fresh pipe pair: two sides, one pipe per direction. -/
private def newPair : IO (Side × Side) := do
  let aToB ← Conc.Pipe.new 4
  let bToA ← Conc.Pipe.new 4
  return ({ read := aToB, write := bToA }, { read := bToA, write := aToB })

/-- A connection over a pipe pair whose far side the test holds and
never writes: the silent peer. The returned pipe is the one the
connection reads, so a check sees the close that wakes the park. -/
private def silentPeer : Async (Streams.Connection × Conc.Pipe) := do
  let toPeer ← Conc.Pipe.new 4
  let fromPeer ← Conc.Pipe.new 4
  return (← pipeConn fromPeer toPeer, fromPeer)

/-- The initiator's marker of the test handshake. -/
private def markerI : ByteArray := Bytes.ofNatList [1, 1, 1, 1]

/-- The responder's marker of the test handshake. -/
private def markerR : ByteArray := Bytes.ofNatList [2, 2, 2, 2]

/-- A validated inline peer id, one per suite peer. An identity
multihash needs no native crypto, so the suite stays portable. -/
private def peerOf (n : Nat) : Libp2p.Identity.PeerId :=
  Libp2p.Identity.PeerId.inline (ByteArray.mk #[n.toUInt8]) (by
    simp [ByteArray.size, Libp2p.Identity.maxInlineKeyBytes])

/-- The fixed peer id of the dialing side. -/
private def dialerId : Libp2p.Identity.PeerId := peerOf 1

/-- The fixed peer id of the listening side. -/
private def listenerId : Libp2p.Identity.PeerId := peerOf 2

/-- The fixed-key plaintext test security value. It replaces the Noise
milestone (#16, unmerged). The handshake writes its marker, reads the
peer's marker from the seed first and then from the connection, and
hands the unconsumed bytes to the next stage. `overread` adds one read
whose chunk joins the leftover, so a check can force the hand-over.
`seedRef` records the seed the negotiation handed over. -/
private def secValue (overread : Bool) (seedRef : Conc.OnceRef (Option ByteArray)) :
    Mock.Core.SecurityProtocol where
  id := ⟨"/test/plain/1.0.0"⟩
  handshake := fun role conn seed => do
    seedRef.set (some seed)
    let myMark := if role = .initiator then markerI else markerR
    let wrote ← (try
      conn.write myMark
      pure true
    catch _ => pure false : Conc.Async Bool)
    if !wrote then throw (.closed "test handshake write failed")
    let seedB := Bytes.toNatList seed
    let rest ←
      if seedB.length ≥ 4 then pure (Bytes.ofNatList (seedB.drop 4))
      else
        match ← conn.read with
        | none => throw (.closed "test handshake read ended before the marker")
        | some chunk => pure (Bytes.ofNatList ((seedB ++ Bytes.toNatList chunk).drop 4))
    let over ←
      if overread then
        match ← conn.read with
        | none => throw (.closed "test handshake over-read found the connection closed")
        | some chunk => pure chunk
      else pure ByteArray.empty
    let pending ← Conc.OnceRef.new (rest ++ over)
    let secureConn : Streams.Connection := { conn with
      read := do
        let bytes ← (pending.updateGet (fun b => (b, ByteArray.empty)) : BaseIO ByteArray)
        if bytes.isEmpty then conn.read else pure (some bytes) }
    return { conn := secureConn,
             localPeer := if role = .initiator then dialerId else listenerId,
             remotePeer := if role = .initiator then listenerId else dialerId,
             leftover := rest ++ over,
             close := Streams.Connection.closeQuietly conn }

/-- The test muxer value. It replaces the yamux milestone (#17,
unmerged). `open` records its leftover argument, the opened id, and a
ran flag in shared cells, and returns a no-op session. -/
private def muxValue (id : Mock.Core.ProtocolId) (ranRef : Conc.OnceRef Bool)
    (leftRef : Conc.OnceRef (Option ByteArray))
    (openRef : Conc.OnceRef (Option Mock.Core.ProtocolId)) : Mock.Core.Muxer where
  id := id
  «open» := fun _ _ leftover => do
    ranRef.set true
    leftRef.set (some leftover)
    openRef.set (some id)
    return { openStream := (throw (.protocol "the test session opens no stream") :
                ExceptT Mock.Core.Error Conc.Async Streams.Stream),
             accept := pure none,
             close := pure (),
             join := pure () }

/-- Wrap a connection so the `n`-th write carries `extra` extra bytes.
The write order is the upgrade's own order: the negotiation frame, the
handshake marker, then the muxer frame. -/
private def appendOnWrite (conn : Streams.Connection) (n : Nat) (extra : ByteArray)
    (count : Conc.OnceRef Nat) : Streams.Connection :=
  { conn with
    write := fun b => do
      let c ← (count.updateGet (fun c => (c, c + 1)) : BaseIO Nat)
      conn.write (if c + 1 = n then b ++ extra else b) }

/-- Wrap a connection so the first write carries the marker after the
negotiation frame, and the second write, the handshake's marker, drops.
The marker then arrives exactly once, through the seed. -/
private def markerViaSeed (conn : Streams.Connection) (count : Conc.OnceRef Nat) :
    Streams.Connection :=
  { conn with
    write := fun b => do
      let c ← (count.updateGet (fun c => (c, c + 1)) : BaseIO Nat)
      if c + 1 = 1 then conn.write (b ++ markerI)
      else if c + 1 = 2 then pure ()
      else conn.write b }

/-- Wrap a connection so the `n`-th write is replaced by `withB`. -/
private def replaceOnWrite (conn : Streams.Connection) (n : Nat) (withB : ByteArray)
    (count : Conc.OnceRef Nat) : Streams.Connection :=
  { conn with
    write := fun b => do
      let c ← (count.updateGet (fun c => (c, c + 1)) : BaseIO Nat)
      conn.write (if c + 1 = n then withB else b) }

/-- Wrap a connection and record every written chunk. -/
private def recordWrites (conn : Streams.Connection) (ref : Conc.OnceRef (List ByteArray)) :
    Streams.Connection :=
  { conn with
    write := fun b => do
      ref.update fun l => b :: l
      conn.write b }

/-- The answer of one upgrade run. -/
private abbrev UpAnswer :=
  Option (Except Mock.Core.Error (Mock.Core.MuxSession × Libp2p.Identity.PeerId))

/-! ## The pipeline checks -/

/-- The full pipeline, both directions, plus the wire-selected muxer
assertion. The test security value carries no advertisement
field, so the wire exchange alone selects the muxer. -/
private def checkFullPipeline (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let dSeed : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lSeed : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator (← sideConn iside) ByteArray.empty
      (some listenerId) [secValue false dSeed] [muxValue muxId dRan dLeft dOpen]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder (← sideConn rside) ByteArray.empty none
      [secValue false lSeed] [muxValue muxId lRan lLeft lOpen]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  match d, l with
  | some (.ok (ds, dp)), some (.ok (ls, lp)) => do
      ds.close
      ls.close
      ds.join
      ls.join
      r.check "upgrade full pipeline dial and listen"
        (dp == listenerId && lp == dialerId)
      r.check "upgrade muxer selected on the wire"
        ((← dOpen.get) == some muxId && (← lOpen.get) == some muxId)
      r.check "upgrade both muxer sessions opened"
        ((← dRan.get) && (← lRan.get))
  | _, _ => do
      r.check "upgrade full pipeline dial and listen" false
      r.check "upgrade muxer selected on the wire" false
      r.check "upgrade both muxer sessions opened" false
  (← sideConn iside).close
  (← sideConn rside).close

/-- The negotiation leftover seeds the handshake: the dialer's first
write carries its marker after the header and proposal, so the
responder's negotiation over-reads the marker and hands it to the
handshake. -/
private def checkNegotiationLeftover (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let count : Conc.OnceRef Nat ← Conc.OnceRef.new 0
  let dSeed : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lSeed : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator (markerViaSeed (← sideConn iside) count)
      ByteArray.empty (some listenerId) [secValue false dSeed]
      [muxValue muxId dRan dLeft dOpen]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder (← sideConn rside) ByteArray.empty none
      [secValue false lSeed] [muxValue muxId lRan lLeft lOpen]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.ok _), some (.ok _) => do
        let s ← lSeed.get
        pure (s == some markerI)
    | _, _ => pure false
  r.check "upgrade leftover negotiation seeds handshake" good
  (← sideConn iside).close
  (← sideConn rside).close

/-- The secure reader delivers bytes the handshake over-read before
the muxer stage reads the connection. -/
private def checkHandshakeLeftover (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator (← sideConn iside) ByteArray.empty
      (some listenerId) [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId dRan dLeft dOpen]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder (← sideConn rside) ByteArray.empty none
      [secValue true (← Conc.OnceRef.new none)] [muxValue muxId lRan lLeft lOpen]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.ok _), some (.ok _) => do
        let lf ← lLeft.get
        let ran ← lRan.get
        pure (lf == some ByteArray.empty && ran)
    | _, _ => pure false
  r.check "upgrade leftover handshake seeds muxer negotiation" good
  (← sideConn iside).close
  (← sideConn rside).close

/-- The muxer negotiation over-reads extra bytes, and they reach
`Muxer.open` as its `ByteArray` argument. -/
private def checkMuxOpenLeftover (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let extra := Bytes.ofNatList [9, 9, 9]
  let count : Conc.OnceRef Nat ← Conc.OnceRef.new 0
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator (appendOnWrite (← sideConn iside) 3 extra count)
      ByteArray.empty (some listenerId) [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId dRan dLeft dOpen]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder (← sideConn rside) ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)] [muxValue muxId lRan lLeft lOpen]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.ok _), some (.ok _) => do
        let lf ← lLeft.get
        pure (lf == some extra)
    | _, _ => pure false
  r.check "upgrade leftover muxer negotiation seeds muxer open" good
  (← sideConn iside).close
  (← sideConn rside).close

/-- The `na` retry: the dialer lists two muxer ids, the responder
supports only the second, and the chosen session is the second id. -/
private def checkNaRetry (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxA : Mock.Core.ProtocolId := ⟨"/test/mux/a"⟩
  let muxB : Mock.Core.ProtocolId := ⟨"/test/mux/b"⟩
  let aRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let aOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let bRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let bOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lWrites : Conc.OnceRef (List ByteArray) ← Conc.OnceRef.new []
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator (← sideConn iside) ByteArray.empty
      (some listenerId) [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxA aRan (← Conc.OnceRef.new none) aOpen,
       muxValue muxB bRan (← Conc.OnceRef.new none) bOpen]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder (recordWrites (← sideConn rside) lWrites)
      ByteArray.empty none [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxB lRan (← Conc.OnceRef.new none) lOpen]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.ok _), some (.ok _) => do
        let bO ← bOpen.get
        let lO ← lOpen.get
        let aO ← aOpen.get
        let aR ← aRan.get
        let lW ← lWrites.get
        pure (bO == some muxB && lO == some muxB && aO == none && !aR &&
          lW.contains (Bytes.ofNatList (encodeMsg (Reply.toMsg .na))))
    | _, _ => pure false
  r.check "upgrade na retry lands on second muxer id" good
  (← sideConn iside).close
  (← sideConn rside).close

/-- The identity mismatch: the dialer fails with authentication before
any muxer byte moves, and the teardown close ends the responder's
parked negotiation with `closed`. -/
private def checkIdentityMismatch (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let wrongId : Libp2p.Identity.PeerId := peerOf 3
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator (← sideConn iside) ByteArray.empty
      (some wrongId) [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId dRan (← Conc.OnceRef.new none) (← Conc.OnceRef.new none)]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder (← sideConn rside) ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId lRan (← Conc.OnceRef.new none) (← Conc.OnceRef.new none)]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.error (.authentication _)), some (.error (.closed _)) => do
        let dR ← dRan.get
        let lR ← lRan.get
        pure (!dR && !lR)
    | _, _ => pure false
  r.check "upgrade identity mismatch fails before muxer open" good
  (← sideConn iside).close
  (← sideConn rside).close

/-- The deadline: a silent peer times out, the teardown closes the
connection, and the parked read ends on its own. -/
private def checkDeadline (r : Runner) : Async Unit := do
  let tc ← Conc.TestClock.new
  let (sc, farPipe) ← silentPeer
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let answer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    answer.set (some (← upgradeWith tc.clock .initiator sc ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId (← Conc.OnceRef.new false) (← Conc.OnceRef.new none)
         (← Conc.OnceRef.new none)]))
  r.check "upgrade deadline arms its timer" (← tc.nextTimer)
  tc.advance Streams.unauthDeadlineMs
  tasks.joinAll
  r.check "upgrade deadline on silent peer times out and closes"
    (match ← answer.get with
     | some (.error (.timeout _)) => true
     | _ => false)
  r.check "upgrade deadline close wakes the silent peer's read"
    ((← farPipe.read) == none)
  tc.close

/-! ## The rejection checks -/

/-- The initiator with no security id to propose fails before any
byte moves. -/
private def checkEmptySecurity (r : Runner) : Async Unit := do
  let tc ← Conc.TestClock.new
  let (sc, _) ← silentPeer
  let answer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    answer.set (some (← upgradeWith tc.clock .initiator sc ByteArray.empty none []
      [muxValue ⟨"/test/mux/1.0.0"⟩ (← Conc.OnceRef.new false) (← Conc.OnceRef.new none)
         (← Conc.OnceRef.new none)]))
  tasks.joinAll
  r.check "upgrade empty security list errors protocol"
    (match ← answer.get with
     | some (.error (.protocol "multistream negotiation failed")) => true
     | _ => false)
  tc.close

/-- The handshake completes, then the initiator with no muxer id to
propose fails, and the teardown close reaches the responder. -/
private def checkEmptyMuxer (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxB : Mock.Core.ProtocolId := ⟨"/test/mux/b"⟩
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tcD ← Conc.TestClock.new
  let tcL ← Conc.TestClock.new
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgradeWith tcD.clock .initiator (← sideConn iside) ByteArray.empty
      (some listenerId) [secValue false (← Conc.OnceRef.new none)] []))
  tasks.spawn do
    lAnswer.set (some (← upgradeWith tcL.clock .responder (← sideConn rside) ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxB lRan (← Conc.OnceRef.new none) (← Conc.OnceRef.new none)]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.error (.protocol "multistream negotiation failed")), some (.error (.closed _)) => do
        let lR ← lRan.get
        pure (!lR)
    | _, _ => pure false
  r.check "upgrade empty muxer list errors protocol" good
  (← sideConn iside).close
  (← sideConn rside).close
  tcD.close
  tcL.close

/-- The peer closes its pipe mid-negotiation: the upgrade answers
`closed`. -/
private def checkEof (r : Runner) : Async Unit := do
  let tc ← Conc.TestClock.new
  let (iside, rside) ← newPair
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let answer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    answer.set (some (← upgradeWith tc.clock .initiator (← sideConn iside) ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId (← Conc.OnceRef.new false) (← Conc.OnceRef.new none)
         (← Conc.OnceRef.new none)]))
  rside.write.close
  tasks.joinAll
  r.check "upgrade EOF during negotiation closed"
    (match ← answer.get with
     | some (.error (.closed _)) => true
     | _ => false)
  tc.close

/-- The responder supports no proposed id: the dialer exhausts its
list and the `negotiationFailed` maps to `protocol`. -/
private def checkExhausted (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxA : Mock.Core.ProtocolId := ⟨"/test/mux/a"⟩
  let muxB : Mock.Core.ProtocolId := ⟨"/test/mux/b"⟩
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tcD ← Conc.TestClock.new
  let tcL ← Conc.TestClock.new
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgradeWith tcD.clock .initiator (← sideConn iside) ByteArray.empty
      (some listenerId) [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxA dRan (← Conc.OnceRef.new none) (← Conc.OnceRef.new none)]))
  tasks.spawn do
    lAnswer.set (some (← upgradeWith tcL.clock .responder (← sideConn rside) ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxB lRan (← Conc.OnceRef.new none) (← Conc.OnceRef.new none)]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  let good ← match d, l with
    | some (.error (.protocol "multistream negotiation failed")), some (.error (.closed _)) => do
        let dR ← dRan.get
        let lR ← lRan.get
        pure (!dR && !lR)
    | _, _ => pure false
  r.check "upgrade exhausted proposals errors protocol" good
  (← sideConn iside).close
  (← sideConn rside).close
  tcD.close
  tcL.close

/-- Malformed bytes on the wire fail the stage as `protocol`, and the
teardown close reaches the peer. -/
private def checkHostile (r : Runner) : Async Unit := do
  let (iside, rside) ← newPair
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let garbage := Bytes.ofNatList (List.replicate 9 255)
  let count : Conc.OnceRef Nat ← Conc.OnceRef.new 0
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tcD ← Conc.TestClock.new
  let tcL ← Conc.TestClock.new
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgradeWith tcD.clock .initiator
      (replaceOnWrite (← sideConn iside) 1 garbage count) ByteArray.empty (some listenerId)
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId (← Conc.OnceRef.new false) (← Conc.OnceRef.new none)
         (← Conc.OnceRef.new none)]))
  tasks.spawn do
    lAnswer.set (some (← upgradeWith tcL.clock .responder (← sideConn rside) ByteArray.empty none
      [secValue false (← Conc.OnceRef.new none)]
      [muxValue muxId (← Conc.OnceRef.new false) (← Conc.OnceRef.new none)
         (← Conc.OnceRef.new none)]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  r.check "upgrade hostile negotiation frame errors protocol"
    (match d, l with
     | some (.error (.closed _)), some (.error (.protocol "multistream decode: malformed")) => true
     | _, _ => false)
  (← sideConn iside).close
  (← sideConn rside).close
  tcD.close
  tcL.close

/-! ## The go trace replays -/

/-- Parse fixture hex through the shared lowercase reader. -/
private def hexOf (h : String) : IO (List Nat) :=
  match Bytes.ofHex? h with
  | some b => pure (Bytes.toNatList b)
  | none => throw <| IO.userError "test fixture hex did not parse"

/-- One captured trace: the initiator-to-responder hexes and the
responder-to-initiator hexes, in write order. -/
private def traceHexes (file : String) (trace : List Json) : IO (List String × List String) := do
  let entries ← trace.mapM fun e => do
    let d ← Tests.jStr file e "dir"
    let h ← Tests.jStr file e "hex"
    pure (d, h)
  pure (entries.filter (·.1 = "i2r") |>.map (·.2), entries.filter (·.1 = "r2i") |>.map (·.2))

/-- The go trace replays through the responder driver: the emitted
writes equal the recorded `r2i` bytes, byte for byte. -/
private def checkGoTraces (r : Runner) : Async Unit := do
  let goj ← Tests.loadJson "mss-go-trace.json"
  let kadId : Mock.Core.ProtocolId := ⟨"/ipfs/kad/1.0.0"⟩
  let fullTrace ← Tests.jArr "mss-go-trace.json" goj "fullTrace"
  let (i2rF, r2iF) ← traceHexes "mss-go-trace.json" fullTrace
  let rs : State := { role := .responder, supported := [kadId], proposals := [],
                      buffer := [], phase := .headerPending }
  let r2iB ← r2iF.mapM (fun h => (hexOf h : Async (List Nat)))
  let chunkF ← hexOf i2rF[0]!
  match drive 2 rs chunkF with
  | .ok (.selected p _ leftover ws) =>
      r.check "upgrade go trace replay through the driver"
        (p == kadId && leftover == [] && ws == r2iB)
  | _ => r.check "upgrade go trace replay through the driver" false

  let naTrace ← Tests.jArr "mss-go-trace.json" goj "naTrace"
  let (i2rN, r2iN) ← traceHexes "mss-go-trace.json" naTrace
  let rn : State := { role := .responder, supported := [], proposals := [],
                      buffer := [], phase := .headerPending }
  let r2iN' ← r2iN.mapM (fun h => (hexOf h : Async (List Nat)))
  let chunkN ← hexOf i2rN[0]!
  match drive 2 rn chunkN with
  | .ok (.running _ _ leftover ws) =>
      r.check "upgrade go na trace replay through the driver"
        (leftover == [] && ws == r2iN')
  | _ => r.check "upgrade go na trace replay through the driver" false

  let lazyTrace ← Tests.jArr "mss-go-trace.json" goj "lazyTrace"
  let (i2rL, _) ← traceHexes "mss-go-trace.json" lazyTrace
  let lazyI2r ← hexOf i2rL[0]!
  match initiatorStart [kadId] with
  | .ok (s, ws) =>
      r.check "upgrade lazy coalesced write"
        (ws == [lazyI2r] && s.phase = .negotiating && s.proposals == [kadId])
  | .error _ => r.check "upgrade lazy coalesced write" false

/-! ## The send-side cap -/

/-- A protocol id whose frame is over the 1 KiB cap. -/
private def overCapId : Mock.Core.ProtocolId :=
  ⟨String.ofList (List.replicate 1100 'a')⟩

/-- A configured id that would produce an over-cap frame is refused before
any byte moves, so the sender cannot emit a frame the decoder rejects. -/
private def checkSendCap (r : Runner) : Async Unit := do
  r.check "negotiate send cap refuses an over-long proposal"
    (match initiatorStart [overCapId] with
     | .error .negotiationFailed => true
     | _ => false)
  r.check "negotiate send cap refuses an over-long supported list"
    (match responderStart [overCapId] with
     | .error .negotiationFailed => true
     | _ => false)
  r.check "negotiate send cap admits a normal id"
    (match initiatorStart [Mock.Core.ProtocolId.mk "/ipfs/kad/1.0.0"] with
     | .ok _ => true
     | _ => false)

/-- The responder writes its header before it reads anything, so a dialer
that also waits does not stall. -/
private def checkResponderFirst (r : Runner) : Async Unit := do
  match responderStart [Mock.Core.ProtocolId.mk "/ipfs/kad/1.0.0"] with
  | .ok (s, ws) =>
      r.check "negotiate responder sends its header first"
        (ws == [encodeMsg header] && s.phase = .negotiating)
  | .error _ => r.check "negotiate responder sends its header first" false

/-! ## The byte-split two-party runs over the sim -/

/-- Record the size of every chunk that a connection's read returns.
The split checks read this to show that the sim delivered one byte at a
time. -/
private def recordReadSizes (conn : Streams.Connection) (sizes : Conc.OnceRef (List Nat)) :
    Streams.Connection :=
  { conn with
    read := do
      match ← conn.read with
      | none => return none
      | some chunk => do
          sizes.update fun l => chunk.size :: l
          return (some chunk) }

/-- A connected pair over a fresh sim net. `split` makes every write of
the net arrive one byte at a time. -/
private def simPair (split : Bool) : Async (Streams.Connection × Streams.Connection) := do
  let net ← Streams.Sim.Net.new split
  let l ← net.transport.listen (← simAddr "/ip4/127.0.0.1/tcp/4101")
  let some dialer ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some listener ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return (dialer, listener)

/-- Read until at least `n` bytes are held, from the seed first and
then from the connection. The answer keeps any extra bytes. A peer that
closes early answers `none`. Under the split sim the marker arrives one
byte per chunk, so the split handshake reads it here. -/
private def readExactly (conn : Streams.Connection) (seed : ByteArray) (n : Nat) :
    Async (Option (List Nat)) := do
  let mut acc := Bytes.toNatList seed
  for _ in [0:n] do
    if acc.length < n then
      match ← conn.read with
      | none => return none
      | some chunk => acc := acc ++ Bytes.toNatList chunk
  return some acc

/-- The fixed-key test handshake, chunk-agnostic: it reads its marker
with `readExactly`, so it accepts whatever chunks the transport chose.
It replaces the Noise milestone (#16, unmerged) as `secValue` does, and
it exists so the pipeline can run over the splitting sim. -/
private def secValueExact (seedRef : Conc.OnceRef (Option ByteArray)) :
    Mock.Core.SecurityProtocol where
  id := ⟨"/test/plain/1.0.0"⟩
  handshake := fun role conn seed => do
    seedRef.set (some seed)
    let myMark := if role = .initiator then markerI else markerR
    let wrote ← (try
      conn.write myMark
      pure true
    catch _ => pure false : Conc.Async Bool)
    if !wrote then throw (.closed "test handshake write failed")
    match ← readExactly conn seed 4 with
    | none => throw (.closed "test handshake read ended before the marker")
    | some four =>
      return { conn := conn,
               localPeer := if role = .initiator then dialerId else listenerId,
               remotePeer := if role = .initiator then listenerId else dialerId,
               leftover := Bytes.ofNatList (four.drop 4),
               close := Streams.Connection.closeQuietly conn }

/-- The multistream exchange of both roles over a splitting sim, for a
supported id and for the `na` retry. Each run also asserts that the
responder's reader saw one byte per chunk, which shows the sim split the
writes. -/
private def checkSplitNegotiate (r : Runner) : Async Unit := do
  let kadId : Mock.Core.ProtocolId := ⟨"/ipfs/kad/1.0.0"⟩
  let idId : Mock.Core.ProtocolId := ⟨"/ipfs/id/1.0.0"⟩
  let runOne (name : String) (iIds rIds : List Mock.Core.ProtocolId)
      (expect : Mock.Core.ProtocolId) : Async Unit := do
    let (ic, rc) ← simPair true
    let sizes : Conc.OnceRef (List Nat) ← Conc.OnceRef.new []
    let split := recordReadSizes rc sizes
    let iReader := Streams.BufReader.new ic
    let rReader := Streams.BufReader.new split
    let iAnswer : Conc.OnceRef (Option (Except Mock.Core.Error StageResult)) ←
      Conc.OnceRef.new none
    let rAnswer : Conc.OnceRef (Option (Except Mock.Core.Error StageResult)) ←
      Conc.OnceRef.new none
    let tasks ← Conc.TaskSet.new
    tasks.spawn do
      iAnswer.set (some (← negotiate .initiator iReader ic ByteArray.empty iIds))
    tasks.spawn do
      rAnswer.set (some (← negotiate .responder rReader split ByteArray.empty rIds))
    tasks.joinAll
    let iAns ← iAnswer.get
    let rAns ← rAnswer.get
    let both := match iAns, rAns with
      | some (.ok i), some (.ok rr) => i.proto == expect && rr.proto == expect
      | _, _ => false
    let seen ← sizes.get
    r.check name both
    r.check s!"{name}, one byte per chunk"
      (!seen.isEmpty && seen.all (fun n => decide (n ≤ 1)))
    ic.close
    rc.close
  runOne "split sim negotiation selects the id in both roles" [kadId] [kadId] kadId
  runOne "split sim negotiation walks the na retry" [kadId, idId] [idId] idId

/-- The whole pipeline over a splitting sim, both directions: the
negotiation, the handshake, the identity check, the muxer negotiation,
and the open. This is the two-party run that the definition of done of
#18 requires. -/
private def checkSplitPipeline (r : Runner) : Async Unit := do
  let (ic, rc) ← simPair true
  let muxId : Mock.Core.ProtocolId := ⟨"/test/mux/1.0.0"⟩
  let dSeed : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lSeed : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let lRan : Conc.OnceRef Bool ← Conc.OnceRef.new false
  let dLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let lLeft : Conc.OnceRef (Option ByteArray) ← Conc.OnceRef.new none
  let dOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let lOpen : Conc.OnceRef (Option Mock.Core.ProtocolId) ← Conc.OnceRef.new none
  let dAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let lAnswer : Conc.OnceRef UpAnswer ← Conc.OnceRef.new none
  let tasks ← Conc.TaskSet.new
  tasks.spawn do
    dAnswer.set (some (← upgrade .initiator ic ByteArray.empty (some listenerId)
      [secValueExact dSeed] [muxValue muxId dRan dLeft dOpen]))
  tasks.spawn do
    lAnswer.set (some (← upgrade .responder rc ByteArray.empty none
      [secValueExact lSeed] [muxValue muxId lRan lLeft lOpen]))
  tasks.joinAll
  let d ← dAnswer.get
  let l ← lAnswer.get
  match d, l with
  | some (.ok (ds, dp)), some (.ok (ls, lp)) => do
      ds.close
      ls.close
      ds.join
      ls.join
      r.check "split sim upgrade pipeline, dial and listen"
        (dp == listenerId && lp == dialerId)
      r.check "split sim upgrade selects the muxer on the wire"
        ((← dOpen.get) == some muxId && (← lOpen.get) == some muxId)
  | _, _ => do
      r.check "split sim upgrade pipeline, dial and listen" false
      r.check "split sim upgrade selects the muxer on the wire" false
  ic.close
  rc.close

/-! ## The suite -/

/-- The suite. -/
def run (r : Runner) : IO Unit := do
  r.section "multistream-select and the upgrader (unit 1b)"
    "packages/libp2p/negotiate/docs/ARCHITECTURE.md"
  let all : Conc.Async Unit := do
    checkFullPipeline r
    checkNegotiationLeftover r
    checkHandshakeLeftover r
    checkMuxOpenLeftover r
    checkNaRetry r
    checkIdentityMismatch r
    checkDeadline r
    checkEmptySecurity r
    checkEmptyMuxer r
    checkEof r
    checkExhausted r
    checkHostile r
    checkSendCap r
    checkResponderFirst r
    checkGoTraces r
    checkSplitNegotiate r
    checkSplitPipeline r
  Conc.Async.run all
  r.skip "upgrade noise yamux matrix over tcp"
    "needs the Noise value and the yamux value, which are not merged on this base (the W5.9 live gate)"

end Tests.Upgrade
