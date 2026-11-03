import Tests.Support
import Libp2p.Negotiate
import Bytes

/-!
# Multistream-select suite (unit 1a)

The wire examples, the `ls` framing, and the captured go traces replay
through the pure core: events in, actions out, no network and no clock
(root §6, the unit 1a milestones of the package plan). The strictness
checks pin every rejection the plan names, and the generic codec
harness runs over `Msg` samples.
-/

set_option autoImplicit false

namespace Tests.Negotiate

open Libp2p.Negotiate
open Bytes (DecodeError)
open Lean (Json)

/-- A test fixture text that fails the suite when it is over the cap. -/
private def msgOf (s : String) : IO Msg :=
  match Msg.ofText? s with
  | some m => pure m
  | none => throw <| IO.userError "test fixture text over the 1 KiB cap"

/-- Parse fixture hex through the shared lowercase reader. -/
private def hexOf (h : String) : IO (List Nat) :=
  match Bytes.ofHex? h with
  | some b => pure (Bytes.toNatList b)
  | none => throw <| IO.userError "test fixture hex did not parse"

/-- The writes of an action list, in order. -/
private def writesOf (actions : List Action) : List (List Nat) :=
  actions.filterMap fun
    | .write bs => some bs
    | .select .. => none

/-- The selects of an action list, in order. -/
private def selectsOf (actions : List Action) : List (Mock.Core.ProtocolId × List Nat) :=
  actions.filterMap fun
    | .select p r => some (p, r)
    | .write _ => none

/-- The responder's initial state. -/
private def responderState (supported : List Mock.Core.ProtocolId) : State :=
  { role := .responder, supported := supported, proposals := [], buffer := [], phase := .headerPending }

/-- The initiator's initial state. -/
private def initiatorState : State :=
  { role := .initiator, supported := [], proposals := [], buffer := [], phase := .headerPending }

/-- Drain the buffer of a state, collecting the actions. The fuel
bounds the walk; the buffer shrinks by one frame per step. -/
private def drain (fuel : Nat) (s : State) : Except Error (State × List Action) :=
  if fuel = 0 then .error .negotiationFailed
  else if s.buffer.isEmpty then .ok (s, [])
  else do
    let (s', actions) ← step s (.bytes [])
    let (s'', rest) ← drain (fuel - 1) s'
    .ok (s'', actions ++ rest)

/-- Replay byte chunks through the core: each chunk is one read event,
then the buffer drains before the next chunk. -/
private def replay (s : State) (chunks : List (List Nat)) : Except Error (State × List Action) :=
  match chunks with
  | [] => .ok (s, [])
  | c :: cs => do
      let (s1, a1) ← step s (.bytes c)
      let (s2, a2) ← drain (s1.buffer.length + 1) s1
      let (s3, a3) ← replay s2 cs
      .ok (s3, a1 ++ a2 ++ a3)

/-- One captured trace: the initiator-to-responder hexes and the
responder-to-initiator hexes, in write order. -/
private def traceHexes (file : String) (trace : List Json) : IO (List String × List String) := do
  let entries ← trace.mapM fun e => do
    let d ← Tests.jStr file e "dir"
    let h ← Tests.jStr file e "hex"
    pure (d, h)
  pure (entries.filter (·.1 = "i2r") |>.map (·.2), entries.filter (·.1 = "r2i") |>.map (·.2))

/-- The suite. -/
def run (r : Runner) : IO Unit := do
  r.section "multistream-select 1.0.0 (unit 1a)" "packages/libp2p/negotiate/docs/ARCHITECTURE.md"

  /- Model-level strictness. -/
  r.check "mss decode zero length malformed"
    (failsWith DecodeError.malformed (decodeMsg? (Mock.Varint.encode (Mock.Varint.boundedVarint 0) ++ [10])))
  r.check "mss decode no trailing newline malformed"
    (failsWith DecodeError.malformed (decodeMsg? (Mock.Varint.encode (Mock.Varint.boundedVarint 2) ++ [110, 97])))
  r.check "mss decode bad UTF-8 malformed"
    (failsWith DecodeError.malformed (decodeMsg? (Mock.Varint.encode (Mock.Varint.boundedVarint 2) ++ [195, 10])))
  r.check "mss decode overlong varint malformed"
    (failsWith DecodeError.malformed (decodeMsg? (List.replicate 12 255)))
  r.check "mss decode short varint truncated"
    (failsWith DecodeError.truncated (decodeMsg? [128]))
  r.check "mss decode short payload truncated"
    (failsWith DecodeError.truncated (decodeMsg? (Mock.Varint.encode (Mock.Varint.boundedVarint 3) ++ [110, 97])))
  r.check "mss decode empty input truncated"
    (failsWith DecodeError.truncated (decodeMsg? []))
  r.check "mss decode cap malformed"
    (failsWith DecodeError.malformed (decodeMsg? (Mock.Varint.encode (Mock.Varint.boundedVarint (maxMsg + 1)) ++ [])))
  r.check "mss decode non-byte model value malformed"
    (failsWith DecodeError.malformed (decodeMsg? (Mock.Varint.encode (Mock.Varint.boundedVarint 2) ++ [300, 10])))
  let mna ← msgOf "na"
  r.check "mss decode suffix"
    (succeedsWith (mna, [7, 8]) (decodeMsg? (encodeMsg mna ++ [7, 8])))
  let kad ← msgOf "/ipfs/kad/1.0.0"
  r.check "mss decode coalesced"
    (succeedsWith (header, encodeText kad.text) (decodeMsg? (encodeMsg header ++ encodeText kad.text)))

  /- The wire vectors. -/
  let wire ← Tests.loadJson "mss-wire.json"
  let cases ← Tests.jArr "mss-wire.json" wire "cases"
  let naHex ← Tests.jStr "mss-wire.json" cases[0]! "bytesHex"
  let naBytes ← hexOf naHex
  r.check "mss wire na encode" (encodeMsg mna == naBytes)
  r.check "mss wire na decode" (succeedsWith (mna, []) (decodeMsg? naBytes))
  let hdrHex ← Tests.jStr "mss-wire.json" cases[1]! "bytesHex"
  let hdrBytes ← hexOf hdrHex
  r.check "mss wire header encode" (encodeMsg header == hdrBytes)
  r.check "mss wire header decode" (succeedsWith (header, []) (decodeMsg? hdrBytes))

  /- The `ls` vector. -/
  let lsj ← Tests.loadJson "mss-ls.json"
  let lsWireHex ← Tests.jStr "mss-ls.json" lsj "lsWireHex"
  let lsBytes ← hexOf lsWireHex
  let mls ← msgOf "ls"
  r.check "mss ls wire encode" (encodeMsg mls == lsBytes)
  r.check "mss ls wire decode" (succeedsWith (mls, []) (decodeMsg? lsBytes))
  let reply ← Tests.jObj "mss-ls.json" lsj "replyExample"
  let protos ← Tests.jStrs "mss-ls.json" reply "protocols"
  let bodyHex ← Tests.jStr "mss-ls.json" reply "bodyHex"
  let bodyBytes ← hexOf bodyHex
  let ids : List Mock.Core.ProtocolId := protos.map fun s => ⟨s⟩
  r.check "mss ls body encode" (lsBody ids == bodyBytes)
  r.check "mss ls reply encode"
    (encodeLs ids == Mock.Varint.encode (Mock.Varint.boundedVarint bodyBytes.length) ++ bodyBytes)
  r.check "mss ls reply decode" (succeedsWith (ids, []) (decodeLs? (encodeLs ids)))

  /- The go traces. -/
  let goj ← Tests.loadJson "mss-go-trace.json"
  let goNaWireHex ← Tests.jStr "mss-go-trace.json" goj "naWireHex"
  let goNaBytes ← hexOf goNaWireHex
  let goHdrWireHex ← Tests.jStr "mss-go-trace.json" goj "headerWireHex"
  let goHdrBytes ← hexOf goHdrWireHex
  r.check "mss go na wire encode" (encodeMsg (Reply.toMsg .na) == goNaBytes)
  r.check "mss go na wire decode" (succeedsWith (Reply.toMsg .na, []) (decodeMsg? goNaBytes))
  r.check "mss go header wire encode" (encodeMsg header == goHdrBytes)
  r.check "mss go header wire decode" (succeedsWith (header, []) (decodeMsg? goHdrBytes))
  let fullTrace ← Tests.jArr "mss-go-trace.json" goj "fullTrace"
  let (i2rF, r2iF) ← traceHexes "mss-go-trace.json" fullTrace
  let naTrace ← Tests.jArr "mss-go-trace.json" goj "naTrace"
  let (i2rN, r2iN) ← traceHexes "mss-go-trace.json" naTrace
  let lazyTrace ← Tests.jArr "mss-go-trace.json" goj "lazyTrace"
  let (i2rL, r2iL) ← traceHexes "mss-go-trace.json" lazyTrace
  let kadId : Mock.Core.ProtocolId := ⟨"/ipfs/kad/1.0.0"⟩
  let nopeId : Mock.Core.ProtocolId := ⟨"/nope/9.9.9"⟩

  match replay (responderState [kadId]) (← i2rF.mapM hexOf) with
  | .error _ => r.check "mss go full trace" false
  | .ok (sf, af) =>
      r.check "mss go full trace"
        (writesOf af == (← r2iF.mapM hexOf) ∧ selectsOf af == [(kadId, [])] ∧ sf.phase = .selected)

  match replay (responderState []) (← i2rN.mapM hexOf) with
  | .error _ => r.check "mss go na trace" false
  | .ok (sn, an) =>
      r.check "mss go na trace"
        (writesOf an == (← r2iN.mapM hexOf) ∧ selectsOf an == [] ∧ sn.phase = .negotiating)

  match replay (responderState [kadId]) (← i2rL.mapM hexOf) with
  | .error _ => r.check "mss go lazy trace" false
  | .ok (sl, al) =>
      r.check "mss go lazy trace"
        (writesOf al == (← r2iL.mapM hexOf) ∧ selectsOf al == [(kadId, [])] ∧ sl.phase = .selected)

  let lazyI2r ← hexOf i2rL[0]!
  match step initiatorState (.propose kadId) with
  | .error _ => r.check "mss go lazy coalesced write" false
  | .ok (s1, a1) =>
      match a1 with
      | [.write w] =>
          r.check "mss go lazy coalesced write"
            (w == lazyI2r ∧ s1.phase = .negotiating ∧ s1.proposals == [kadId])
      | _ => r.check "mss go lazy coalesced write" false

  match step initiatorState (.propose kadId) with
  | .error _ => r.check "mss go initiator lazy select" false
  | .ok (s1, _) =>
      match replay s1 (← r2iL.mapM hexOf) with
      | .error _ => r.check "mss go initiator lazy select" false
      | .ok (s2, a2) =>
          r.check "mss go initiator lazy select"
            (s2.phase = .selected ∧ selectsOf a2 == [(kadId, [])] ∧ writesOf a2 == [])

  /- Step-level checks. -/
  let sNeg : State := { role := .responder, supported := [], proposals := [], buffer := [], phase := .negotiating }
  match step sNeg (.bytes (encodeText nopeId.toString)) with
  | .error _ => r.check "mss step responder unknown id writes na and stays negotiating" false
  | .ok (s', actions) =>
      r.check "mss step responder unknown id writes na and stays negotiating"
        (s'.phase = .negotiating ∧ actions == [.write (encodeMsg (Reply.toMsg .na))])

  let sup : List Mock.Core.ProtocolId := [⟨"/ipfs/kad/1.0.0"⟩, ⟨"/ipfs/id/1.0.0"⟩]
  let sSup : State := { role := .responder, supported := sup, proposals := [], buffer := [], phase := .negotiating }
  match step sSup (.bytes (encodeText "ls")) with
  | .error _ => r.check "mss step responder ls writes ls reply and stays negotiating" false
  | .ok (s', actions) =>
      r.check "mss step responder ls writes ls reply and stays negotiating"
        (s'.phase = .negotiating ∧ actions == [.write (encodeLs sup)])

  let sInit : State := { role := .initiator, supported := [], proposals := [kadId, nopeId], buffer := [], phase := .awaitingAnswer }
  match step sInit (.bytes (encodeText "na")) with
  | .error _ => r.check "mss step initiator na advances proposal list" false
  | .ok (s', actions) =>
      r.check "mss step initiator na advances proposal list"
        (s'.proposals == [nopeId] ∧ actions == [.write (encodeText nopeId.toString)])

  let sOne : State := { role := .initiator, supported := [], proposals := [kadId], buffer := [], phase := .awaitingAnswer }
  r.check "mss step initiator proposals exhausted errors"
    (failsWith Error.negotiationFailed (step sOne (.bytes (encodeText "na"))))

  r.check "mss step hostile frame errors"
    (failsWith (Error.decode .malformed)
      (step sNeg (.bytes (Mock.Varint.encode (Mock.Varint.boundedVarint (maxMsg + 1)) ++ []))))

  let sBuf : State := { role := .responder, supported := [], proposals := [], buffer := [], phase := .negotiating }
  match step sBuf (.bytes [128]) with
  | .error _ => r.check "mss step truncated waits" false
  | .ok (s', actions) =>
      r.check "mss step truncated waits" (actions == [] ∧ s'.phase = .negotiating ∧ s'.buffer == [128])

  let sKad : State := { role := .responder, supported := [kadId], proposals := [], buffer := [], phase := .negotiating }
  match step sKad (.bytes (encodeText kadId.toString ++ [99])) with
  | .error _ => r.check "mss step select leftover conservation" false
  | .ok (s', actions) =>
      r.check "mss step select leftover conservation"
        (s'.phase = .selected ∧ actions == [.write (encodeText kadId.toString), .select kadId [99]])

  match step sNeg (.bytes (List.replicate 8 255)), step sNeg (.bytes (List.replicate 9 255)) with
  | .ok (s1, a1), .error e2 =>
      r.check "mss step hostile buffer bounded"
        (a1 == [] ∧ e2 == Error.decode .malformed ∧ s1.buffer == List.replicate 8 255)
  | _, _ => r.check "mss step hostile buffer bounded" false

  /- The generic harness. -/
  let ipfsId ← msgOf "/ipfs/id/1.0.0"
  let samples : List Msg := [Reply.toMsg .na, Reply.toMsg .ls, header, kad, ipfsId]
  r.check "mss generic round-trip harness" (Bytes.checkRoundTrips samples == true)

  r.skip "mss generic model pin"
    "needs the ByteArray adapter, a stretch item this pull request defers; the model decoder is the production path today"

end Tests.Negotiate
