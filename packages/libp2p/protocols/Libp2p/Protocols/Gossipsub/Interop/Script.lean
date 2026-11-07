import Lean
import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Protocols.Gossipsub.Interop.MessageId

/-!
# GossipSub interop script parser

This module implements specification sections 2 and 3. It parses the script
object and all seven v1.1 instruction forms. It reports the instruction path
and field when decoding fails. The two v1.2 partial-message forms return an
explicit out-of-scope error.

The parser uses a fuel argument for nested instructions. This gives a total
parser with a clear maximum nesting depth and avoids a partial definition.
Missing parameter fields stay as options and therefore select Core.defaults.
The raw field retains every source pair. The unmapped field retains fields
without a Core home, including HeartbeatInitialDelay. Exact decimal integer
division truncates nanoseconds toward zero: 100100000 ns becomes 100 ms.
GossipFactor scales a fraction by 100 and truncates to Core's integer percent.
The harness model declares a float; its JVM adapter defaults it to 0.25
(ScriptInstruction.kt:89). Negative mapped numbers and invalid cache windows
return errors. The supported nesting depth is 256 instructions. An unknown parameter name
returns an error, so a future harness field stays visible instead of becoming
an unrecorded default.

prepareScript selects conditional instructions for one node and requires its
initialization first. waitComplete compares elapsed seconds with a deadline.
The later IO driver must keep message processing active while that guard is false.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

open Lean
open Libp2p.Protocols.Gossipsub

/-- One parsed GossipSub parameter object, with all supplied fields retained. -/
structure GossipSubParams where
  d : Option Nat
  dLow : Option Nat
  dHigh : Option Nat
  dScore : Option Nat
  dLazy : Option Nat
  historyLength : Option Nat
  historyGossip : Option Nat
  gossipFactor : Option JsonNumber
  heartbeatInitialDelay : Option JsonNumber
  heartbeatInterval : Option JsonNumber
  fanoutTtl : Option JsonNumber
  pruneBackoff : Option JsonNumber
  raw : List (String × Json)
  unmapped : List (String × Json)

/-- The seven supported script instruction forms. -/
inductive Instruction where
  | initGossipSub (params : GossipSubParams)
  | ifNodeIDEquals (nodeId : Int) (instruction : Instruction)
  | connect (connectTo : List Int)
  | subscribeToTopic (topicId : String) (isPartial : Bool)
  | publish (messageId : Int) (messageSizeBytes : Int) (topicId : String)
  | setTopicValidationDelay (topicId : String) (delaySeconds : Float)
  | waitUntil (elapsedSeconds : Int)

/-- The complete script value. -/
structure Script where
  instructions : List Instruction

/-- Convert a JSON value to object pairs while adding a readable path. -/
def objectPairs (path : String) (value : Json) : Except String (List (String × Json)) :=
  match value.getObj? with
  | .ok object => .ok object.toList
  | .error _ => .error s!"{path}: expected object"

/-- Find one object field without confusing a missing field with a bad type. -/
def field? (path : String) (value : Json) (name : String) : Except String (Option Json) :=
  match objectPairs path value with
  | .error error => .error error
  | .ok pairs => .ok (pairs.find? (fun pair => pair.1 == name) |>.map (fun pair => pair.2))

/-- Read one required field. -/
def requiredField (path : String) (value : Json) (name : String) : Except String Json :=
  match field? path value name with
  | .error error => .error error
  | .ok (some result) => .ok result
  | .ok none => .error s!"{path}: missing field {name}"

/-- Read one optional field. -/
def optionalField (path : String) (value : Json) (name : String) : Except String (Option Json) :=
  field? path value name

/-- Decode a required natural number. -/
def requiredNat (path : String) (value : Json) (name : String) : Except String Nat :=
  let fieldPath := s!"{path}.{name}"
  match requiredField path value name with
  | .error error => .error error
  | .ok field =>
      match field.getNat? with
      | .ok result => .ok result
      | .error _ => .error s!"{fieldPath}: expected integer"

/-- Decode an optional natural number. -/
def optionalNat (path : String) (value : Json) (name : String) : Except String (Option Nat) :=
  match optionalField path value name with
  | .error error => .error error
  | .ok none => .ok none
  | .ok (some field) =>
      match field.getNat? with
      | .ok result => .ok (some result)
      | .error _ => .error s!"{path}.{name}: expected integer"

/-- Decode a required signed integer. -/
def requiredInt (path : String) (value : Json) (name : String) : Except String Int :=
  match requiredField path value name with
  | .error error => .error error
  | .ok field =>
      match field.getInt? with
      | .ok result => .ok result
      | .error _ => .error s!"{path}.{name}: expected integer"

/-- Decode a required string. -/
def requiredString (path : String) (value : Json) (name : String) : Except String String :=
  match requiredField path value name with
  | .error error => .error error
  | .ok field =>
      match field.getStr? with
      | .ok result => .ok result
      | .error _ => .error s!"{path}.{name}: expected string"

/-- Decode a required boolean. -/
def requiredBool (path : String) (value : Json) (name : String) : Except String Bool :=
  match requiredField path value name with
  | .error error => .error error
  | .ok field =>
      match field.getBool? with
      | .ok result => .ok result
      | .error _ => .error s!"{path}.{name}: expected boolean"

/-- Decode a required JSON number as a Float. -/
def requiredFloat (path : String) (value : Json) (name : String) : Except String Float :=
  match requiredField path value name with
  | .error error => .error error
  | .ok field =>
      match field.getNum? with
      | .ok result => .ok result.toFloat
      | .error _ => .error s!"{path}.{name}: expected number"

/-- Decode a nonnegative decimal parameter without a binary float conversion. -/
private def optionalNumber (path : String) (value : Json) (name : String) :
    Except String (Option JsonNumber) := do
  match ← optionalField path value name with
  | none => return none
  | some field =>
      let number ← field.getNum?.mapError (fun _ => s!"{path}.{name}: expected number")
      if number.mantissa < 0 then
        throw s!"{path}.{name}: expected nonnegative number"
      return some number

/-- Decode one parameter object and keep every source pair. -/
def parseGossipSubParams (path : String) (value : Json) : Except String GossipSubParams := do
  let pairs ← objectPairs path value
  let getNat (name : String) := optionalNat path value name
  let d ← getNat "D"
  let dLow ← getNat "Dlo"
  let dHigh ← getNat "Dhi"
  let dScore ← getNat "Dscore"
  let dLazy ← getNat "Dlazy"
  let historyLength ← getNat "HistoryLength"
  let historyGossip ← getNat "HistoryGossip"
  let gossipFactor ← optionalNumber path value "GossipFactor"
  let heartbeatInitialDelay ← optionalNumber path value "HeartbeatInitialDelay"
  let heartbeatInterval ← optionalNumber path value "HeartbeatInterval"
  let fanoutTtl ← optionalNumber path value "FanoutTTL"
  let pruneBackoff ← optionalNumber path value "PruneBackoff"
  let mapped := ["D", "Dlo", "Dhi", "Dscore", "Dlazy", "HistoryLength", "HistoryGossip",
    "GossipFactor", "HeartbeatInterval", "FanoutTTL", "PruneBackoff"]
  let retained := ["Dout", "GossipRetransmission", "HeartbeatInitialDelay", "SlowHeartbeatWarning",
    "PrunePeers", "UnsubscribeBackoff", "Connectors", "MaxPendingConnections", "ConnectionTimeout",
    "DirectConnectTicks", "DirectConnectInitialDelay", "OpportunisticGraftTicks", "OpportunisticGraftPeers",
    "GraftFloodThreshold", "MaxIHaveLength", "MaxIHaveMessages", "MaxIDontWantLength", "MaxIDontWantMessages",
    "IWantFollowupTime", "IDontWantMessageThreshold", "IDontWantMessageTTL"]
  return {
    d := d
    dLow := dLow
    dHigh := dHigh
    dScore := dScore
    dLazy := dLazy
    historyLength := historyLength
    historyGossip := historyGossip
    gossipFactor := gossipFactor
    heartbeatInitialDelay := heartbeatInitialDelay
    heartbeatInterval := heartbeatInterval
    fanoutTtl := fanoutTtl
    pruneBackoff := pruneBackoff
    raw := pairs
    unmapped := ← pairs.filterMapM fun pair =>
      if mapped.contains pair.1 then pure none
      else if retained.contains pair.1 then pure (some pair)
      else throw s!"{path}: unknown parameter {pair.1}"
  }

/-- Convert harness nanoseconds to Core milliseconds by truncating. -/
def nanosecondsToMillis (value : JsonNumber) : Nat :=
  value.mantissa.toNat / (10 ^ value.exponent * 1000000)

/-- Convert the harness fraction to Core's integer percent field. -/
def gossipFactorToPercent (value : JsonNumber) : Nat :=
  (value.mantissa.toNat * 100) / 10 ^ value.exponent

/-- Build a cache window only when its required bound holds. -/
def validWindow (historyLength historyGossip : Nat) : Option Cache.WindowParams :=
  if proof : 0 < historyGossip ∧ historyGossip ≤ historyLength then
    some { historyLength := historyLength, historyGossip := historyGossip, valid := proof }
  else
    none

/-- Apply parsed parameters to Core.defaults and install the interop id rule. -/
def toCoreParams (params : GossipSubParams) : Except String Core.Params := do
  let base := Core.defaults
  let historyLength := params.historyLength.getD base.window.historyLength
  let historyGossip := params.historyGossip.getD base.window.historyGossip
  let window ← match validWindow historyLength historyGossip with
    | some value => pure value
    | none => throw "gossipSubParams.HistoryGossip: expected 0 < HistoryGossip ≤ HistoryLength"
  return { base with
    mesh := { base.mesh with
      d := params.d.getD base.mesh.d
      dLow := params.dLow.getD base.mesh.dLow
      dHigh := params.dHigh.getD base.mesh.dHigh
      dScore := params.dScore.getD base.mesh.dScore
      dLazy := params.dLazy.getD base.mesh.dLazy }
    heartbeatInterval := params.heartbeatInterval.map nanosecondsToMillis |>.getD base.heartbeatInterval
    fanoutTtl := params.fanoutTtl.map nanosecondsToMillis |>.getD base.fanoutTtl
    pruneBackoff := params.pruneBackoff.map nanosecondsToMillis |>.getD base.pruneBackoff
    gossipFactor := params.gossipFactor.map gossipFactorToPercent |>.getD base.gossipFactor
    window := window
    msgId := msgIdFn }

/-- Decode a required integer list with indexed field errors. -/
def parseIntList (path : String) (values : List Json) (index : Nat) : Except String (List Int) :=
  match values with
  | [] => .ok []
  | value :: rest =>
      match value.getInt? with
      | .error _ => .error s!"{path}[{index}]: expected integer"
      | .ok result =>
          match parseIntList path rest (index + 1) with
          | .error error => .error error
          | .ok tail => .ok (result :: tail)

/-- Decode one instruction with bounded recursive fuel. -/
def parseInstructionFuel : Nat → String → Json → Except String Instruction
  | 0, path, _ => .error s!"{path}: nesting limit exceeded"
  | fuel + 1, path, value => do
      let kind ← requiredString path value "type"
      match kind with
      | "initGossipSub" =>
          let params ← requiredField path value "gossipSubParams"
          .initGossipSub <$> parseGossipSubParams s!"{path}.gossipSubParams" params
      | "ifNodeIDEquals" =>
          let nodeId ← requiredInt path value "nodeID"
          let nested ← requiredField path value "instruction"
          let instruction ← parseInstructionFuel fuel s!"{path}.instruction" nested
          .ok (.ifNodeIDEquals nodeId instruction)
      | "connect" =>
          let field ← requiredField path value "connectTo"
          match field.getArr? with
          | .error _ => .error s!"{path}.connectTo: expected array"
          | .ok values => .connect <$> parseIntList s!"{path}.connectTo" values.toList 0
      | "subscribeToTopic" =>
          let topicId ← requiredString path value "topicID"
          let isPartial ← match optionalField path value "partial" with
            | .error error => .error error
            | .ok none => .ok false
            | .ok (some field) => match field.getBool? with
              | .ok result => .ok result
              | .error _ => .error s!"{path}.partial: expected boolean"
          .ok (.subscribeToTopic topicId isPartial)
      | "publish" =>
          let messageId ← requiredInt path value "messageID"
          let messageSizeBytes ← requiredInt path value "messageSizeBytes"
          let topicId ← requiredString path value "topicID"
          .ok (.publish messageId messageSizeBytes topicId)
      | "setTopicValidationDelay" =>
          let topicId ← requiredString path value "topicID"
          let delaySeconds ← requiredFloat path value "delaySeconds"
          .ok (.setTopicValidationDelay topicId delaySeconds)
      | "waitUntil" =>
          .waitUntil <$> requiredInt path value "elapsedSeconds"
      | "addPartialMessage" =>
          .error s!"{path}: addPartialMessage is out of scope for v1.1"
      | "publishPartial" | "publishToNodeIDs" =>
          .error s!"{path}: {kind} is out of scope for v1.1"
      | _ => .error s!"{path}.type: unknown instruction type {kind}"

/-- Decode one instruction with the module's bounded nesting depth. -/
def parseInstruction (path : String) (value : Json) : Except String Instruction :=
  parseInstructionFuel 256 path value

/-- Decode a JSON script object. -/
def parseScriptJson (value : Json) : Except String Script := do
  let field ← requiredField "root" value "script"
  let values ← match field.getArr? with
    | .ok result => .ok result.toList
    | .error _ => .error "root.script: expected array"
  let rec loop (index : Nat) (remaining : List Json) : Except String (List Instruction) :=
    match remaining with
    | [] => .ok []
    | item :: rest => do
        let instruction ← parseInstruction s!"script[{index}]" item
        let tail ← loop (index + 1) rest
        return instruction :: tail
  return { instructions := ← loop 0 values }

/-- Parse a complete params.json string. -/
def parseScript (source : String) : Except String Script := do
  let value ← Json.parse source
  parseScriptJson value

/-- Resolve a chain of node conditions without changing instruction order. -/
def instructionForNode (nodeId : Int) : Instruction → Option Instruction
  | .ifNodeIDEquals expected nested =>
      if nodeId == expected then instructionForNode nodeId nested else none
  | instruction => some instruction

/-- Separate startup parameters from the remaining instructions for one node. -/
def prepareScript (nodeId : Int) (script : Script) :
    Except String (GossipSubParams × List Instruction) := do
  let selected := script.instructions.filterMap (instructionForNode nodeId)
  match selected with
  | .initGossipSub params :: rest =>
      if rest.any (fun instruction => match instruction with
          | .initGossipSub _ => true
          | _ => false) then
        throw "script: initGossipSub must occur only at startup"
      let _ ← toCoreParams params
      return (params, rest)
  | _ => throw "script: initGossipSub must precede every other instruction"

/-- A wait releases the next instruction once elapsed seconds reach its deadline.
The IO driver continues delivery and forwarding between calls to this guard. -/
def waitComplete (elapsedSeconds deadlineSeconds : Int) : Bool :=
  decide (elapsedSeconds ≥ deadlineSeconds)

end Libp2p.Protocols.Gossipsub.Interop
