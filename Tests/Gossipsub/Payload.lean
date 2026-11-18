import Tests.Support
import Libp2p.Protocols.Gossipsub.Payload
import Libp2p.Protocols.Gossipsub.Core

/-!
# Gossipsub suite: the `ByteArray` payload path

This suite pins `Payload.splitInbound` and `Payload.joinOutbound` to the
model codec over random RPCs (CLAUDE.md, "Proofs and tests", rule 2):

* The model decode of the split RPC equals the model decode of the
  original with each message's `data` replaced by its handle. The split
  returns the payloads by id.
* The model decode of the joined bytes equals the original RPC.

Two checks name the split errors: a payload with no id, and a truncated
RPC.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Payload

open Libp2p.Protocols.Gossipsub

private def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- The test's id function: the topic's length, the payload's length,
and its first four bytes. -/
private def idOf (topic : String) (d : ByteArray) : MessageId :=
  ⟨[topic.length % 256, d.size % 256, d.size / 256 % 256] ++ (d.extract 0 4).toList.map (·.toNat)⟩

/-- A random RPC: up to three messages with payloads of up to 600
bytes on two topics, a subscription, and an IHAVE. -/
private def randomRpc (seed : Nat) : Rpc.RPC × Nat := Id.run do
  let mut s := seed
  let mut msgs : List Message := []
  s := lcg s
  for _ in [0:(s / 7) % 4] do
    s := lcg s
    let len := (s / 11) % 600
    let mut data : List Nat := []
    for _ in [0:len] do
      s := lcg s
      data := ((s / 13) % 256) :: data
    s := lcg s
    let topic : TopicId := if (s / 17) % 2 == 0 then ⟨"blocks"⟩ else ⟨"columns_3"⟩
    msgs := msgs ++ [{ «from» := none, data := some data, seqno := none, topic,
                       signature := none, key := none }]
  let control : Option Rpc.ControlMessage :=
    some { ihave := [{ topicId := "blocks", messageIds := [⟨[1, 2, 3]⟩] }], iwant := [], graft := [],
           prune := [] }
  return ({ subscriptions := [{ subscribe := true, topicid := "blocks" }], publish := msgs,
            control }, s)

private def decode (b : ByteArray) : Option Rpc.RPC :=
  (Core.decodeRpc (Bytes.toNatList b)).toOption

/-- The original with each message's data replaced by its handle. -/
private def withHandles (r : Rpc.RPC) : Rpc.RPC :=
  { r with publish := r.publish.map fun m =>
      { m with data := some (idOf m.topic.name (Bytes.ofNatList (m.data.getD []))).bytes } }

def run (r : Runner) : IO Unit := do
  r.section "gossipsub Payload" "gossipsub-v1.0.md, the protobuf; the model codec of Rpc.lean"
  let mut seed := 3
  let mut splitOk := true
  let mut joinOk := true
  for _ in [0:300] do
    let (rpc, s) := randomRpc seed
    seed := s
    let raw := Bytes.ofNatList (Pb.encodeMessage rpc)
    match Payload.splitInbound raw (fun t d => some (idOf t d)) with
    | .error _ => splitOk := false
    | .ok (small, payloads) =>
      if decode small != some (withHandles rpc) then splitOk := false
      let expected := rpc.publish.map fun m =>
        let d := Bytes.ofNatList (m.data.getD [])
        (idOf m.topic.name d, d)
      if payloads.map (fun (i, d) => (i, d.toList)) != expected.map (fun (i, d) => (i, d.toList)) then
        splitOk := false
      let lookup (h : MessageId) : Option ByteArray := (payloads.find? (·.1 == h)).map (·.2)
      if decode (Payload.joinOutbound (withHandles rpc) lookup) != some rpc then joinOk := false
  r.check "payload: the split RPC decodes to the original with handles, payloads by id" splitOk
  r.check "payload: the joined bytes decode to the original RPC" joinOk
  -- One message with data, so the id function runs once.
  let one : Rpc.RPC := { subscriptions := [], control := none, publish :=
    [{ «from» := none, data := some [1, 2, 3], seqno := none, topic := ⟨"blocks"⟩,
       signature := none, key := none }] }
  let oneRaw := Bytes.ofNatList (Pb.encodeMessage one)
  r.check "payload: a payload with no id fails the split with noId"
    (match Payload.splitInbound oneRaw (fun _ _ => none) with
     | .error .noId => true
     | _ => false)
  r.check "payload: a truncated RPC fails the split with malformed"
    (match Payload.splitInbound (oneRaw.extract 0 (oneRaw.size - 1)) (fun t d => some (idOf t d)) with
     | .error .malformed => true
     | _ => false)

end Tests.Gossipsub.Payload
