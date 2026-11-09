import Tests.Support
import Libp2p.Protocols.Gossipsub.Interop

/-!
# GossipSub interop pure-core suite

This suite checks the adapter against the captured 32-node script and the
pure edge cases required by specification sections 2, 3, 5, 6, and 7.
The fixture count is top-level 100. Recursive instruction counts include the
80 conditional wrappers and their nested instructions, so they total 180.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Interop

open Lean (Json)
open Tests (Runner loadFixture)
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Interop

private def fixture : String := "gossipsub-interop-params.json"

structure Counts where
  total : Nat := 0
  ifNode : Nat := 0
  init : Nat := 0
  connect : Nat := 0
  subscribe : Nat := 0
  publish : Nat := 0
  validationDelay : Nat := 0
  wait : Nat := 0

private def add (left right : Counts) : Counts :=
  { total := left.total + right.total
    ifNode := left.ifNode + right.ifNode
    init := left.init + right.init
    connect := left.connect + right.connect
    subscribe := left.subscribe + right.subscribe
    publish := left.publish + right.publish
    validationDelay := left.validationDelay + right.validationDelay
    wait := left.wait + right.wait }

private def countInstruction : Instruction → Counts
  | .initGossipSub _ => { total := 1, init := 1 }
  | .ifNodeIDEquals _ nested => add { total := 1, ifNode := 1 } (countInstruction nested)
  | .connect _ => { total := 1, connect := 1 }
  | .subscribeToTopic _ _ => { total := 1, subscribe := 1 }
  | .publish _ _ _ => { total := 1, publish := 1 }
  | .setTopicValidationDelay _ _ => { total := 1, validationDelay := 1 }
  | .waitUntil _ => { total := 1, wait := 1 }

private def countInstructions (instructions : List Instruction) : Counts :=
  instructions.foldl (fun counts instruction => add counts (countInstruction instruction)) {}

private def firstInit : List Instruction → Option GossipSubParams
  | [] => none
  | .initGossipSub params :: _ => some params
  | .ifNodeIDEquals _ nested :: rest => firstInit (nested :: rest)
  | _ :: rest => firstInit rest

private def firstNested : List Instruction → Option Instruction
  | [] => none
  | .ifNodeIDEquals nodeId nested :: _ => some (.ifNodeIDEquals nodeId nested)
  | _ :: rest => firstNested rest

private def hasConnect : List Instruction → Bool
  | [] => false
  | .connect peers :: _ => !peers.isEmpty
  | .ifNodeIDEquals _ nested :: rest => hasConnect (nested :: rest)
  | _ :: rest => hasConnect rest

private def hasSubscribe : List Instruction → Bool
  | [] => false
  | .subscribeToTopic topic isPartial :: _ => topic == "a-subnet" && !isPartial
  | .ifNodeIDEquals _ nested :: rest => hasSubscribe (nested :: rest)
  | _ :: rest => hasSubscribe rest

private def hasPublish : List Instruction → Bool
  | [] => false
  | .publish messageId size topic :: _ => messageId == 0 && size == 98304 && topic == "a-subnet"
  | .ifNodeIDEquals _ nested :: rest => hasPublish (nested :: rest)
  | _ :: rest => hasPublish rest

private def hasDelay : List Instruction → Bool
  | [] => false
  | .setTopicValidationDelay topic delay :: _ => topic == "a-subnet" && delay == 0.005
  | .ifNodeIDEquals _ nested :: rest => hasDelay (nested :: rest)
  | _ :: rest => hasDelay rest

private def hasWait : List Instruction → Bool
  | [] => false
  | .waitUntil seconds :: rest => seconds == 342 || hasWait rest
  | .ifNodeIDEquals _ nested :: rest => hasWait (nested :: rest)
  | _ :: rest => hasWait rest

private def parsedJson (source : String) : Json :=
  match Json.parse source with
  | .ok value => value
  | .error _ => Json.null

private def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def errorIs {α : Type} (message : String) : Except String α → Bool
  | .error error => error == message
  | .ok _ => false

private def stringField (value : Json) (name : String) : Option String :=
  match value.getObjVal? name with
  | .ok field => field.getStr?.toOption
  | .error _ => none

private def intField (value : Json) (name : String) : Option Int :=
  match value.getObjVal? name with
  | .ok field => field.getInt?.toOption
  | .error _ => none

/-- The fixture, instruction fields, and parameter conversion. -/
private def checkScript (r : Runner) : IO Unit := do
  r.section "gossipsub interop script" "vendor/test-plans/gossipsub-interop/script_instruction.py"
  let fixtureJson ← loadFixture fixture
  let parsed := parseScriptJson fixtureJson
  match parsed with
  | .error _ =>
      r.check "captured script parses" false
  | .ok script =>
      let counts := countInstructions script.instructions
      r.check "top-level instruction count" (script.instructions.length == 100)
      r.check "recursive instruction count" (counts.total == 180)
      r.check "ifNodeIDEquals count" (counts.ifNode == 80)
      r.check "initGossipSub count" (counts.init == 32)
      r.check "connect count" (counts.connect == 32)
      r.check "publish count" (counts.publish == 16)
      r.check "waitUntil count" (counts.wait == 18)
      r.check "setTopicValidationDelay count" (counts.validationDelay == 1)
      r.check "subscribeToTopic count" (counts.subscribe == 1)
      r.check "connect fields decode" (hasConnect script.instructions)
      r.check "subscribe fields decode" (hasSubscribe script.instructions)
      r.check "publish fields decode" (hasPublish script.instructions)
      r.check "validation delay fields decode" (hasDelay script.instructions)
      r.check "wait fields decode" (hasWait script.instructions)
      match firstNested script.instructions with
      | some (.ifNodeIDEquals nodeId (.initGossipSub _)) =>
          r.check "nested node id decodes" (nodeId == 0)
      | _ => r.check "nested instruction decodes" false
      match firstInit script.instructions with
      | none => r.check "captured parameters present" false
      | some params =>
          r.check "captured parameter pair retained" (params.raw.length == 1)
          r.check "HeartbeatInitialDelay retained" (params.heartbeatInitialDelay.map nanosecondsToMillis == some 100)
          r.check "HeartbeatInitialDelay is not mapped" (match toCoreParams params with
            | .ok core => core.heartbeatInterval == Core.defaults.heartbeatInterval
            | .error _ => false)
          r.check "HeartbeatInitialDelay is unmapped" (params.unmapped.length == 1 &&
            params.unmapped.any (fun pair => pair.1 == "HeartbeatInitialDelay"))

/-- Each unsupported and malformed input returns a typed parse error. -/
private def checkErrors (r : Runner) : IO Unit := do
  r.check "script scalar rejected" (errorIs "root.script: expected array" (parseScript "{\"script\":5}"))
  r.check "unknown instruction rejected" (errorIs "script[0].type: unknown instruction type nope" (parseScript "{\"script\":[{\"type\":\"nope\"}]}"))
  r.check "publish missing topic rejected" (isError (parseScriptJson (parsedJson "{\"script\":[{\"type\":\"publish\",\"messageID\":1,\"messageSizeBytes\":8}]}")))
  r.check "connect non-integer rejected" (isError (parseScriptJson (parsedJson "{\"script\":[{\"type\":\"connect\",\"connectTo\":[\"x\"]}]}")))
  r.check "addPartialMessage rejected explicitly"
    (errorIs "script[0]: addPartialMessage is out of scope for v1.1"
      (parseScriptJson (parsedJson "{\"script\":[{\"type\":\"addPartialMessage\"}]}")))
  r.check "publishPartial rejected explicitly"
    (errorIs "script[0]: publishPartial is out of scope for v1.1"
      (parseScriptJson (parsedJson "{\"script\":[{\"type\":\"publishPartial\"}]}")))

/-- The record encoder emits compact, escaped JSON objects. -/
private def checkRecords (r : Runner) : IO Unit := do
  let peer := peerIdLine "2026-11-06T00:00:00Z" "peer" 3
  let received := receivedMessageLine "2026-11-06T00:00:00Z" 31 (some "peer\"\\") (some "topic\"\\")
  r.check "PeerID line exact shape"
    (peer == "{\"id\":\"peer\",\"msg\":\"PeerID\",\"node_id\":3,\"time\":\"2026-11-06T00:00:00Z\"}")
  r.check "PeerID line has required fields"
    (stringField (parsedJson peer) "msg" == some "PeerID" && intField (parsedJson peer) "node_id" == some 3)
  r.check "received line exact shape"
    (received == "{\"from\":\"peer\\\"\\\\\",\"id\":\"31\",\"msg\":\"Received Message\",\"time\":\"2026-11-06T00:00:00Z\",\"topic\":\"topic\\\"\\\\\"}")
  r.check "received line parses back"
    (stringField (parsedJson received) "topic" == some "topic\"\\" && stringField (parsedJson received) "id" == some "31")
  r.check "records stay single line" (!peer.contains '\n' && !received.contains '\n')
/-- The message id and node address edge cases. -/
private def checkIds (r : Runner) : IO Unit := do
  r.check "message id one" (messageIdString [0, 0, 0, 0, 0, 0, 0, 1] == "1")
  r.check "message id maximum" (messageIdString [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] == "18446744073709551615")
  r.check "message id big endian" (messageIdString [1, 0, 0, 0, 0, 0, 0, 0] == "72057594037927936")
  r.check "short message id is right padded" (messageIdString [1] == "72057594037927936")
  r.check "node zero" (nodeId? "node0" == some 0)
  r.check "node thirty one" (nodeId? "node31" == some 31)
  r.check "node without number rejected" (nodeId? "node" == none)
  r.check "leading zero rejected" (nodeId? "node01" == none)
  r.check "negative node rejected" (nodeId? "node-1" == none)
  r.check "uppercase node rejected" (nodeId? "Node1" == none)
  r.check "suffix text rejected" (nodeId? "node1x" == none)
  r.check "empty hostname rejected" (nodeId? "" == none)
  r.check "overflow node rejected" (nodeId? "node18446744073709551616" == none)
  r.check "peer seed is 32 bytes" ((peerSeed 31).length == 32)
  r.check "peer seed uses little endian" ((peerSeed 31).take 8 == [31, 0, 0, 0, 0, 0, 0, 0])


/-- All mapped fields, retained fields, and pure scheduling contracts. -/
private def checkParameters (r : Runner) : IO Unit := do
  let json := parsedJson "{\"D\":8,\"Dlo\":6,\"Dhi\":14,\"Dscore\":5,\"Dlazy\":7,\"HistoryLength\":9,\"HistoryGossip\":4,\"GossipFactor\":0.255,\"HeartbeatInitialDelay\":100100000,\"HeartbeatInterval\":100100000,\"FanoutTTL\":1201000000,\"PruneBackoff\":2001999999,\"Dout\":2}"
  match parseGossipSubParams "params" json with
  | .error _ => r.check "all parameter fields parse" false
  | .ok params =>
      r.check "all source parameter pairs retained" (params.raw.length == 13)
      r.check "unsupported fields retained" (params.unmapped.map Prod.fst ==
        ["Dout", "HeartbeatInitialDelay"])
      match toCoreParams params with
      | .error _ => r.check "valid parameters map" false
      | .ok core =>
          r.check "mesh D maps" (core.mesh.d == 8)
          r.check "mesh Dlo maps" (core.mesh.dLow == 6)
          r.check "mesh Dhi maps" (core.mesh.dHigh == 14)
          r.check "mesh Dscore maps" (core.mesh.dScore == 5)
          r.check "mesh Dlazy maps" (core.mesh.dLazy == 7)
          r.check "heartbeat truncates nanoseconds" (core.heartbeatInterval == 100)
          r.check "fanout truncates nanoseconds" (core.fanoutTtl == 1201)
          r.check "prune truncates nanoseconds" (core.pruneBackoff == 2001)
          r.check "gossip fraction truncates percent" (core.gossipFactor == 25)
          r.check "history length maps" (core.window.historyLength == 9)
          r.check "history gossip maps" (core.window.historyGossip == 4)
          let message : Message := {
            «from» := none
            data := some [0,0,0,0,0,0,0,1,9]
            seqno := none
            topic := ⟨"topic"⟩
            signature := none
            key := none }
          r.check "core message id uses eight bytes" ((core.msgId message).bytes == [0,0,0,0,0,0,0,1])
  match parseGossipSubParams "params" (parsedJson "{}") with
  | .error _ => r.check "empty parameters parse" false
  | .ok params =>
      match toCoreParams params with
      | .error _ => r.check "defaults map" false
      | .ok core =>
          let defaults := Core.defaults
          r.check "absent mesh fields use defaults" (core.mesh == defaults.mesh)
          r.check "absent times use defaults" (core.heartbeatInterval == defaults.heartbeatInterval &&
            core.fanoutTtl == defaults.fanoutTtl && core.pruneBackoff == defaults.pruneBackoff)
          r.check "absent cache uses defaults" (core.window.historyLength == defaults.window.historyLength &&
            core.window.historyGossip == defaults.window.historyGossip)
  r.check "unknown parameter rejected" (isError
    (parseGossipSubParams "params" (parsedJson "{\"FutureField\":1}")))
  r.check "negative parameter rejected" (isError
    (parseGossipSubParams "params" (parsedJson "{\"HeartbeatInterval\":-1}")))
  match parseGossipSubParams "params" (parsedJson "{\"HistoryLength\":1,\"HistoryGossip\":2}") with
  | .error _ => r.check "invalid cache bound rejected" false
  | .ok params => r.check "invalid cache bound rejected" (isError (toCoreParams params))
  r.check "exact conversion near millisecond boundary"
    (nanosecondsToMillis ⟨999999999999999999, 3⟩ == 999999999)
  r.check "fractional nanosecond truncates" (nanosecondsToMillis ⟨1001000005, 1⟩ == 100)
  r.check "wait blocks before deadline" (!waitComplete 119 120)
  r.check "wait releases at deadline" (waitComplete 120 120)
  r.check "wait releases after deadline" (waitComplete 121 120)
  let captured ← loadFixture fixture
  match parseScriptJson captured with
  | .error _ => r.check "startup script parses" false
  | .ok script =>
      for nodeId in List.range 32 do
        r.check s!"node {nodeId} initializes first" (match prepareScript nodeId script with
          | .ok (_, rest) => !rest.isEmpty
          | .error _ => false)
      r.check "missing startup rejected" (isError (prepareScript 32 script))
  let late := parseScript "{\"script\":[{\"type\":\"waitUntil\",\"elapsedSeconds\":0},{\"type\":\"initGossipSub\",\"gossipSubParams\":{}}]}"
  r.check "late initialization rejected" (match late with
    | .ok script => isError (prepareScript 0 script)
    | .error _ => false)
  r.check "partial default false" (match parseInstruction "i"
      (parsedJson "{\"type\":\"subscribeToTopic\",\"topicID\":\"t\"}") with
    | .ok (.subscribeToTopic topic flag) => topic == "t" && !flag
    | _ => false)
  r.check "partial explicit true retained" (match parseInstruction "i"
      (parsedJson "{\"type\":\"subscribeToTopic\",\"topicID\":\"t\",\"partial\":true}") with
    | .ok (.subscribeToTopic _ flag) => flag
    | _ => false)
  let topic := "quote\"slash\\line\nreturn\rtab\t" ++ String.singleton (Char.ofNat 1)
  let line := receivedMessageLine "2026-11-06T00:00:00Z" 1 none (some topic)
  r.check "all control characters escape" (!line.contains '\n' && !line.contains '\r' &&
    !line.contains '\t' && stringField (parsedJson line) "topic" == some topic)
  r.check "empty message id zero" (messageIdString [] == "0")
  r.check "message tail does not change id" (messageIdString [0,0,0,0,0,0,0,1,255] == "1")
  r.check "maximum node accepted" (nodeId? "node18446744073709551615" == some 18446744073709551615)
  r.check "seed spans all eight bytes" ((peerSeed 72623859790382856).take 8 == [8,7,6,5,4,3,2,1])
  r.check "seed suffix zero" ((peerSeed 72623859790382856).drop 8 == List.replicate 24 0)

/-- The decoder preserves recursion and reports the exact failing field. -/
private def checkDecoderDetails (r : Runner) : IO Unit := do
  let source ← IO.FS.readFile "Tests/fixtures/gossipsub-interop-params.json"
  r.check "captured source parses through Json.parse" (match parseScript source with
    | .ok script => script.instructions.length == 100
    | .error _ => false)
  r.check "missing publish topic names field"
    (errorIs "script[0]: missing field topicID"
      (parseScript "{\"script\":[{\"type\":\"publish\",\"messageID\":1,\"messageSizeBytes\":8}]}"))
  r.check "bad connect element names index"
    (errorIs "script[0].connectTo[1]: expected integer"
      (parseScript "{\"script\":[{\"type\":\"connect\",\"connectTo\":[1,\"x\"]}]}"))
  r.check "partial publish alias rejected explicitly"
    (errorIs "script[0]: publishToNodeIDs is out of scope for v1.1"
      (parseScript "{\"script\":[{\"type\":\"publishToNodeIDs\"}]}"))
  r.check "nested condition recurses twice" (match parseInstruction "i"
      (parsedJson "{\"type\":\"ifNodeIDEquals\",\"nodeID\":7,\"instruction\":{\"type\":\"ifNodeIDEquals\",\"nodeID\":7,\"instruction\":{\"type\":\"waitUntil\",\"elapsedSeconds\":42}}}") with
    | .ok instruction => match instructionForNode 7 instruction with
      | some (.waitUntil seconds) => seconds == 42
      | _ => false
    | _ => false)
  r.check "nested bad field includes full path" (errorIs "i.instruction: missing field elapsedSeconds"
    (parseInstruction "i" (parsedJson "{\"type\":\"ifNodeIDEquals\",\"nodeID\":0,\"instruction\":{\"type\":\"waitUntil\"}}")))
  r.check "bounded decoder rejects excess nesting" (isError
    (parseInstructionFuel 1 "i" (parsedJson "{\"type\":\"ifNodeIDEquals\",\"nodeID\":0,\"instruction\":{\"type\":\"waitUntil\",\"elapsedSeconds\":1}}")))
  let minimal := receivedMessageLine "2026-11-06T00:00:00Z" 18446744073709551615 none none
  r.check "received optional fields omitted" (minimal ==
    "{\"id\":\"18446744073709551615\",\"msg\":\"Received Message\",\"time\":\"2026-11-06T00:00:00Z\"}")

/-- Hosts parsing and exact name resolution. -/
private def checkHosts (r : Runner) : IO Unit := do
  let shadow := "127.0.0.1 localhost\n11.0.0.1 node0\n11.0.0.2 node1 node-one n1 # aliases\n11.0.0.3 node10\n"
  let hosts := parseHosts shadow
  r.check "Shadow hosts IPv4 rows parse" (hosts.length == 4)
  r.check "primary name lookup" (lookup? hosts "node0" == some [11,0,0,1])
  r.check "alias lookup" (lookup? hosts "node-one" == some [11,0,0,2])
  r.check "missing name lookup" (lookup? hosts "node2" == none)
  r.check "prefix node1 does not match node10" (lookup? hosts "node1" == some [11,0,0,2])
  r.check "suffix node1x does not match" (lookup? hosts "node1x" == none)
  r.check "CRLF and whitespace parse" (lookup? (parseHosts " 11.0.0.4\tnode4\r\n") "node4" == some [11,0,0,4])
  r.check "IPv6 row ignored" (lookup? (parseHosts "::1 localhost\n") "localhost" == none)
  r.check "malformed row ignored" (lookup? (parseHosts "11.0.0 node-bad\n") "node-bad" == none)
  r.check "comment and blank rows ignored" (parseHosts "# only\n\n   # tail\n" == [])
  r.check "multiaddr prefix" (multiaddrPrefix [11,0,0,2] == some "/ip4/11.0.0.2/tcp/9000")

private def nondecreasing : List ScheduledAction → Bool
  | [] | [_] => true
  | left :: right :: rest => left.time ≤ right.time && nondecreasing (right :: rest)

private structure FixturePublish where
  messageId : Nat
  nodeId : Nat
  time : Nat
  size : Nat
  topic : String
  deriving BEq, DecidableEq

private def publishRowsFor (script : Script) (nodeId : Nat) : List FixturePublish :=
  match plan script (Int.ofNat nodeId) with
  | .error _ => []
  | .ok actions => actions.filterMap fun item => match item.action with
    | .publish id size topic => some ⟨id.toNat, nodeId, item.time, size.toNat, topic⟩
    | _ => none

private def allPublishRows (script : Script) : List FixturePublish :=
  (List.range 32).flatMap (publishRowsFor script)

private def publishRowsForPlan (script : Script) (nodeId : Nat) : List (Nat × Nat × Nat × String) :=
  match plan script (Int.ofNat nodeId) with
  | .error _ => []
  | .ok actions => actions.filterMap fun item => match item.action with
    | .publish id size topic => some (item.time, id.toNat, size.toNat, topic)
    | _ => none

private def waitPlan (source : String) : Option (List ScheduledAction) :=
  match parseScript source with
  | .error _ => none
  | .ok script => (plan script 0).toOption

private def checkPlan (r : Runner) : IO Unit := do
  let source ← loadFixture fixture
  match parseScriptJson source with
  | .error _ => r.check "virtual plan parses fixture" false
  | .ok script =>
      match plan script 0, plan script 0, plan script 1, plan script 2, plan script 31 with
      | .ok node0, .ok again, .ok node1, .ok node2, .ok node31 =>
          r.check "virtual plan is deterministic" (node0 == again)
          r.check "node pruning differs" (node0 != node2 && node2 != node31)
          r.check "node0 first action is init at t=0" (match node0.head? with
            | some action =>
                action.time == 0 && (match action.action with
                | .initGossipSub _ => true
                | _ => false)
            | none => false)
          let node0Publishes := node0.filterMap fun item => match item.action with
            | .publish _ _ _ => some item.time
            | _ => none
          r.check "node0 has zero publishes in this fixture" (node0Publishes == [])
          let publishes := node2.filterMap fun item => match item.action with
            | .publish id size topic => some (item.time, id.toNat, size.toNat, topic)
            | _ => none
          r.check "node2 has three publishes" (publishes.length == 3)
          r.check "node2 publish times and fields" (publishes ==
            [(168000, 4, 98304, "a-subnet"), (180000, 5, 98304, "a-subnet"),
             (252000, 11, 98304, "a-subnet")])
          r.check "node 1 publish subset empty" (publishRowsForPlan script 1 == [])
          r.check "node 2 publish subset exact" (publishRowsForPlan script 2 ==
            [(168000, 4, 98304, "a-subnet"), (180000, 5, 98304, "a-subnet"),
             (252000, 11, 98304, "a-subnet")])
          r.check "node 3 publish subset exact" (publishRowsForPlan script 3 ==
            [(132000, 1, 98304, "a-subnet"), (264000, 12, 98304, "a-subnet")])
          r.check "node 16 publish subset exact" (publishRowsForPlan script 16 ==
            [(228000, 9, 98304, "a-subnet"), (288000, 14, 98304, "a-subnet")])
          r.check "node 31 publish subset empty" (publishRowsForPlan script 31 == [])
          r.check "publish count per node" (((List.range 32).filterMap fun nodeId =>
            let count := (publishRowsFor script nodeId).length
            if count == 0 then none else some (nodeId, count)) ==
              [(2,3), (3,2), (5,1), (6,1), (7,1), (8,1), (16,2), (17,1), (20,1), (27,1), (28,1), (30,1)])
          r.check "all 32 node plans succeed" ((List.range 32).all fun nodeId =>
            (plan script (Int.ofNat nodeId)).isOk)
          let publishRows := allPublishRows script
          let publishIds := publishRows.map (·.messageId)
          r.check "fixture has exactly 16 publishes" (publishRows.length == 16)
          r.check "publish IDs cover 0 through 15 exactly once" (publishIds.length == 16 &&
            publishIds.eraseDups.length == 16 && publishIds.all (fun id => id ≤ 15))
          r.check "all publish sizes and topics match fixture" (publishRows.all (fun row => row.size == 98304 && row.topic == "a-subnet"))
          r.check "all 16 fixture publishes stay attached to their nodes" (allPublishRows script ==
            [⟨4, 2, 168000, 98304, "a-subnet"⟩,
             ⟨5, 2, 180000, 98304, "a-subnet"⟩,
             ⟨11, 2, 252000, 98304, "a-subnet"⟩,
             ⟨1, 3, 132000, 98304, "a-subnet"⟩,
             ⟨12, 3, 264000, 98304, "a-subnet"⟩,
             ⟨10, 5, 240000, 98304, "a-subnet"⟩,
             ⟨3, 6, 156000, 98304, "a-subnet"⟩,
             ⟨15, 7, 300000, 98304, "a-subnet"⟩,
             ⟨6, 8, 192000, 98304, "a-subnet"⟩,
             ⟨9, 16, 228000, 98304, "a-subnet"⟩,
             ⟨14, 16, 288000, 98304, "a-subnet"⟩,
             ⟨8, 17, 216000, 98304, "a-subnet"⟩,
             ⟨13, 20, 276000, 98304, "a-subnet"⟩,
             ⟨0, 27, 120000, 98304, "a-subnet"⟩,
             ⟨7, 28, 204000, 98304, "a-subnet"⟩,
             ⟨2, 30, 144000, 98304, "a-subnet"⟩])
          r.check "node0 subscribe is full at t=0" (node0.any fun item => item.time == 0 && match item.action with
            | .subscribeToTopic topic isPartial => topic == "a-subnet" && !isPartial
            | _ => false)
          r.check "validation delay is topic scoped at 5ms" (node0.any fun item => match item.action with
            | .setTopicValidationDelay topic delay => topic == "a-subnet" && delay == 5 && item.time == 0
            | _ => false)
          r.check "node0 connects at t=0" (node0.any fun item => item.time == 0 && match item.action with
            | .connect _ => true
            | _ => false)
          r.check "node0 wait reaches 342s" (node0.any fun item => match item.action with
            | .waitUntil deadline => deadline == 342 && item.time == 342000
            | _ => false)
          r.check "node0 has no action after 342s" (node0.all (fun item => item.time ≤ 342000))
          r.check "node1 has full startup and wait sequence" (node1.length == 22 &&
            node1.head?.map (fun item => item.time == 0) == some true &&
            node1.getLast?.map (fun item => item.time == 342000) == some true)
          r.check "node31 has full startup and wait sequence" (node31.length == 22 &&
            node31.head?.map (fun item => item.time == 0) == some true &&
            node31.getLast?.map (fun item => item.time == 342000) == some true)
          let reverseWait := waitPlan "{\"script\":[{\"type\":\"initGossipSub\",\"gossipSubParams\":{}},{\"type\":\"waitUntil\",\"elapsedSeconds\":300},{\"type\":\"waitUntil\",\"elapsedSeconds\":100},{\"type\":\"connect\",\"connectTo\":[]}] }"
          r.check "earlier wait barrier remains at t=300" (match reverseWait with
            | some actions => nondecreasing actions && actions.length == 4 &&
                actions[2]?.map (·.time) == some 300000 && actions.getLast?.map (·.time) == some 300000
            | none => false)
          r.check "action after earlier wait stays at t=300" (match reverseWait with
            | some actions => actions.getLast?.map (fun item => match item.action with
                | .connect _ => item.time == 300000
                | _ => false) == some true
            | none => false)
          let sameWait := waitPlan "{\"script\":[{\"type\":\"initGossipSub\",\"gossipSubParams\":{}},{\"type\":\"waitUntil\",\"elapsedSeconds\":300},{\"type\":\"waitUntil\",\"elapsedSeconds\":300}] }"
          r.check "equal wait barrier is idempotent" (match sameWait with
            | some actions => actions.length == 3 && actions[1]?.map (·.time) == some 300000 &&
                actions[2]?.map (·.time) == some 300000
            | none => false)
          let zeroWait := waitPlan "{\"script\":[{\"type\":\"initGossipSub\",\"gossipSubParams\":{}},{\"type\":\"waitUntil\",\"elapsedSeconds\":0},{\"type\":\"connect\",\"connectTo\":[]}] }"
          r.check "zero wait as first action adds no delay" (match zeroWait with
            | some actions => actions.length == 3 && actions.all (fun item => item.time == 0)
            | none => false)
          r.check "positive waits never move virtual time backwards" (match plan script 0 with
            | .ok actions => nondecreasing actions
            | .error _ => false)
      | _, _, _, _, _ =>
          r.check "virtual plan builds for nodes 0, 1, 2, and 31" false

/-- The suite. -/
def run (r : Runner) : IO Unit := do
  checkScript r
  checkErrors r
  checkRecords r
  checkIds r
  checkParameters r
  checkDecoderDetails r
  checkHosts r
  checkPlan r

end Tests.Gossipsub.Interop
