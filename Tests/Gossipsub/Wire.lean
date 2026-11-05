import Tests.Support
import Libp2p.Protocols.Gossipsub.Rpc

/-!
# Gossipsub suite: the wire bytes of the reference implementation

`Tests/fixtures/gossipsub-rpc-go.json` records nine gossipsub RPC values that the pinned go
implementation marshals with its own protobuf encoder. Each case carries the marshaled payload as
hex, the semantic values the generator set, and a `roundtrip` flag that the generator confirmed
with `proto.Unmarshal` and `proto.Equal`. The generator is
`packages/libp2p/protocols/tools/go-rpc-fixtures/main.go`, and the module version comes from the
interop harness pin (`vendor/test-plans/gossipsub-interop/go-libp2p/go.mod:8`).

This suite decodes each case with this package's codec, checks the decoded value against the
recorded fields, and re-encodes it. The re-encoding decodes to the same value, and for every case
whose payload carries no field that this codec leaves out, the re-encoding is the recorded bytes.
The suite reads one fixture and needs no network, no clock and no task.

The plan records that gossipsub has no vectors (`docs/PLAN.md`, "Vector stance"). This fixture is
the first one, and its home is `Tests/fixtures` rather than `Tests/vectors`, because a random
draw does not reproduce it; the generator records where every byte came from.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Wire

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Rpc
open Tests (Runner loadFixture jArr jObj jStr unhex)

open Lean (Json)

private def file : String := "gossipsub-rpc-go.json"

/-- The recorded provenance names this repository's generator, the go module, and the pinned
version, so a fixture that arrives from somewhere else fails its own check. -/
private def checkProvenance (r : Runner) (j : Json) : IO Unit := do
  let p ← jObj file j "_provenance"
  let expect (field got : String) (want : String) : IO Unit :=
    r.check s!"wire provenance {field}" (got == want)
  expect "generatedBy" (← jStr file p "generatedBy")
    "packages/libp2p/protocols/tools/go-rpc-fixtures/main.go"
  expect "module" (← jStr file p "module") "github.com/libp2p/go-libp2p-pubsub, pb package"
  expect "version" (← jStr file p "version") "v0.15.1-0.20260305223556-a01777894f4c"

/-- The bytes of a hex string in the fixture. -/
private def bytesOf (what hex : String) : IO (List Nat) := do
  return Bytes.toNatList (← unhex what hex)

/-- Decode one payload. The answer is `none` when the codec rejects bytes that the go encoder
produced, which is the failure this suite exists to find. -/
private def decodePayload (r : Runner) (what : String) (payload : ByteArray) :
    IO (Option Rpc.RPC) :=
  match Pb.decodeMessage? (α := Rpc.RPC) (Bytes.toNatList payload) with
  | .ok (rpc, rest) => do
    r.check s!"{what} consumes every byte" rest.isEmpty
    return some rpc
  | .error _ => do
    r.check s!"{what} decodes" false
    return none

/-- The value survives one re-encoding: this codec's encoder output decodes to the same value. -/
private def isStable (rpc : Rpc.RPC) : Bool :=
  match Pb.decodeMessage? (α := Rpc.RPC) (Pb.encodeMessage rpc) with
  | .ok (again, rest) => (again == rpc) && rest.isEmpty
  | .error _ => false

/-- The `fields` object of one case, when the case carries one. -/
private def fieldsOf (c : Json) : IO (Option Json) :=
  match c.getObjVal? "fields" with
  | .ok v => return some v
  | .error _ => return none

/-- The subscription records the generator set, checked against the decoded value. -/
private def checkSubs (r : Runner) (name : String) (f : Json) (rpc : Rpc.RPC) : IO Unit := do
  let arr := match (f.getObjVal? "subscriptions") with
    | .ok v => (v.getArr?.toOption.getD #[]).toList
    | .error _ => []
  r.check s!"{name} subscription count" (arr.length == rpc.subscriptions.length)
  for (rec, got) in arr.zip rpc.subscriptions do
    let topicid := (rec.getObjVal? "topicid").toOption.bind (·.getStr?.toOption)
    let sub := (rec.getObjVal? "subscribe").toOption.bind (·.getBool?.toOption)
    r.check s!"{name} subscription topic" (topicid == some got.topicid)
    r.check s!"{name} subscription flag" (sub == some got.subscribe)

/-- The published messages the generator set, checked against the decoded value. -/
private def checkPubs (r : Runner) (name : String) (f : Json) (rpc : Rpc.RPC) : IO Unit := do
  let arr := match (f.getObjVal? "publish") with
    | .ok v => (v.getArr?.toOption.getD #[]).toList
    | .error _ => []
  r.check s!"{name} publish count" (arr.length == rpc.publish.length)
  for (rec, got) in arr.zip rpc.publish do
    let topic := (rec.getObjVal? "topic_str").toOption.bind (·.getStr?.toOption)
    r.check s!"{name} publish topic" (topic == some got.topic.name)
    let dataHex : Option String := (rec.getObjVal? "data_hex").toOption.bind (·.getStr?.toOption)
    match dataHex with
    | some h => r.check s!"{name} publish data" (some (Bytes.toNatList (Bytes.ofHex? h |>.getD .empty)) == got.data)
    | none => r.check s!"{name} publish data absent" got.data.isNone

/-- The control counts and the prune record of the topic, which is the only control message that
carries a peer list and a backoff here. -/
private def checkControl (r : Runner) (name : String) (f : Json) (rpc : Rpc.RPC) : IO Unit := do
  match f.getObjVal? "control" with
  | .error _ => r.check s!"{name} no control when none was set" rpc.control.isNone
  | .ok c =>
    match rpc.control with
    | none => r.check s!"{name} control decodes" false
    | some msg =>
      let count (k : String) : IO Nat := do
        match c.getObjVal? k with
        | .ok v => return (v.getArr?.toOption.getD #[]).size
        | .error _ => return 0
      let ngraft ← count "graft"
      let nprune ← count "prune"
      let nihave ← count "ihave"
      let niwant ← count "iwant"
      r.check s!"{name} graft count" (ngraft == msg.graft.length)
      r.check s!"{name} prune count" (nprune == msg.prune.length)
      r.check s!"{name} ihave count" (nihave == msg.ihave.length)
      r.check s!"{name} iwant count" (niwant == msg.iwant.length)
      if let some p := msg.prune.head? then
        r.check s!"{name} prune topic" (p.topicId == "test-topic")
        r.check s!"{name} prune backoff" (p.backoff == some 60)
        r.check s!"{name} prune peers" (p.peers.map (·.peerId) == [some [1, 2, 3]])
      if let some i := msg.ihave.head? then
        r.check s!"{name} ihave topic" (i.topicId == "test-topic")
        r.check s!"{name} ihave ids"
          (i.messageIds.map (·.bytes) == [[1, 0, 0, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0]])
      if let some i := msg.iwant.head? then
        r.check s!"{name} iwant ids"
          (i.messageIds.map (·.bytes) == [[1, 0, 0, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0]])

/-- One case: decode, check the recorded fields, re-encode, and compare the bytes. The
`unknown-fields` case carries a field this codec leaves out on the way back, so its re-encoding is
a prefix of the recorded bytes, and that is the recorded behaviour rather than a surprise. -/
private def checkCase (r : Runner) (c : Json) : IO Unit := do
  let name ← jStr file c "name"
  let payload ← bytesOf s!"{file} {name}" (← jStr file c "hex")
  let rtRecorded := (c.getObjVal? "roundtrip").toOption.bind (·.getBool?.toOption)
  r.check s!"{name} generator roundtrip" (rtRecorded == some true)
  match ← decodePayload r name (Bytes.ofNatList payload) with
  | none => pure ()
  | some rpc =>
    r.check s!"{name} re-encodes stably" (isStable rpc)
    if let some f ← fieldsOf c then
      checkSubs r name f rpc
      checkPubs r name f rpc
      checkControl r name f rpc
    let encoded := Pb.encodeMessage rpc
    if name == "unknown-fields" then
      r.check s!"{name} re-encoding is the recorded prefix"
        (encoded.length < payload.length && payload.take encoded.length == encoded)
    else
      r.check s!"{name} re-encoding is the recorded bytes" (encoded == payload)

/-- The suite. -/
def run (r : Runner) : IO Unit := do
  r.section "gossipsub wire" "tests/fixtures/gossipsub-rpc-go.json"
  let j ← loadFixture file
  checkProvenance r j
  let cases ← jArr file j "cases"
  r.check "wire case count" (cases.length == 9)
  for c in cases do
    checkCase r c

end Tests.Gossipsub.Wire