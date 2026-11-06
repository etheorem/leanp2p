import Libp2p.Protocols.Gossipsub.Interop.Script

/-!
# GossipSub interop virtual clock

The pure core needs a dry run over the captured 342 second scenario before
any IO driver exists. `plan` is that dry run: it selects one node's
instructions with `prepareScript`, projects each instruction to an `Action`,
and stamps every action with the virtual time a driver would reach it at.

A `waitUntil` instruction is a barrier, not an action the node sleeps
through. The virtual clock jumps to the deadline and the actions behind the
wait inherit the new time. The IO driver keeps the same contract: it calls
`waitComplete` between its ticks while delivery and forwarding continue.

`GossipSubParams` carries `Lean.Json` values, which have no `BEq` instance,
so `Action.beq` compares the parsed fields directly. Two scripts that parse
to the same fields therefore produce plans the test can compare for
determinism.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

/-- Virtual time in milliseconds, matching the gossipsub core's `Millis`. -/
abbrev Millis := Nat

/-- One instruction the selected node executes, without the node conditions. -/
inductive Action where
  | initGossipSub (params : GossipSubParams)
  | connect (peers : List Int)
  | subscribeToTopic (topic : String) (isPartial : Bool)
  | publish (messageId size : Int) (topic : String)
  | setTopicValidationDelay (topic : String) (delayMillis : Nat)
  | waitUntil (deadlineSeconds : Int)

/-- One action and the virtual time it executes at. -/
structure ScheduledAction where
  time : Millis
  action : Action

/-- Compare two parameter objects by their parsed fields, since `Json` has no `BEq`. -/
private def sameParams : GossipSubParams → GossipSubParams → Bool
  | left, right => left.raw == right.raw && left.unmapped == right.unmapped
    && left.heartbeatInitialDelay == right.heartbeatInitialDelay
    && left.heartbeatInterval == right.heartbeatInterval
    && left.fanoutTtl == right.fanoutTtl && left.pruneBackoff == right.pruneBackoff
    && left.historyLength == right.historyLength && left.historyGossip == right.historyGossip
    && left.gossipFactor == right.gossipFactor && left.d == right.d && left.dLow == right.dLow
    && left.dHigh == right.dHigh && left.dScore == right.dScore && left.dLazy == right.dLazy

/-- Structural equality over actions, field by field. -/
def Action.beq : Action → Action → Bool
  | .initGossipSub left, .initGossipSub right => sameParams left right
  | .connect left, .connect right => left == right
  | .subscribeToTopic lTopic lPartial, .subscribeToTopic rTopic rPartial =>
      lTopic == rTopic && lPartial == rPartial
  | .publish lId lSize lTopic, .publish rId rSize rTopic =>
      lId == rId && lSize == rSize && lTopic == rTopic
  | .setTopicValidationDelay lTopic lDelay, .setTopicValidationDelay rTopic rDelay =>
      lTopic == rTopic && lDelay == rDelay
  | .waitUntil left, .waitUntil right => left == right
  | _, _ => false

instance : BEq Action := ⟨Action.beq⟩

instance : BEq ScheduledAction where
  beq left right := left.time == right.time && left.action == right.action

/-- Flatten node conditions away and convert a validation delay to milliseconds.

The delay arrives as a `Float` in seconds. The nearest whole millisecond,
floored toward zero, keeps `0.005` at exactly 5 ms. -/
private def actionOf : Instruction → Action
  | .initGossipSub params => .initGossipSub params
  | .ifNodeIDEquals _ nested => actionOf nested
  | .connect peers => .connect peers
  | .subscribeToTopic topic isPartial => .subscribeToTopic topic isPartial
  | .publish id size topic => .publish id size topic
  | .setTopicValidationDelay topic delay =>
      .setTopicValidationDelay topic (Float.floor (delay * 1000.0)).toUInt64.toNat
  | .waitUntil deadline => .waitUntil deadline

/-- Stamp each instruction with the virtual time a driver reaches it at.

The clock starts at zero. A `waitUntil` moves the clock to its deadline in
milliseconds. A negative deadline would move the clock backwards, so it
clamps to the current time instead. -/
private def expand (clock : Millis) : List Instruction → List ScheduledAction
  | [] => []
  | instruction :: rest =>
      match instruction with
      | .waitUntil deadline =>
          let next := if deadline ≤ 0 then clock else deadline.toNat * 1000
          { time := next, action := actionOf instruction } :: expand next rest
      | _ => { time := clock, action := actionOf instruction } :: expand clock rest

/-- Build the virtual-clock plan for one node.

The plan starts with the startup `initGossipSub` at time zero, because the
harness states every node initializes before any other instruction. The
remaining actions keep script order. `waitComplete` is the guard the live
driver pairs with each `waitUntil` in this list. -/
def plan (script : Script) (nodeId : Int) : Except String (List ScheduledAction) := do
  let (params, selected) ← prepareScript nodeId script
  let start := { time := 0, action := Action.initGossipSub params }
  pure (start :: expand 0 selected)

end Libp2p.Protocols.Gossipsub.Interop
