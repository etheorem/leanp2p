import Lean

/-!
# GossipSub interop NDJSON records

This module implements specification section 5. It turns one event and one
RFC 3339 time string into one compact JSON object. The result has no trailing
line feed. The JSON encoder escapes quotes, backslashes, and control bytes,
so each result stays one NDJSON line. Object keys use the core tree-map
ordering. The harness reads named JSON fields, so their order carries no
meaning. The caller supplies an RFC 3339 timestamp. The received event takes
a UInt64 so its id always becomes an unsigned decimal string. Each call
emits one event, including when the caller passes a duplicate message.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

open Lean

/-- Events required by the interop output contract. -/
inductive RecordEvent where
  | peerId (id : String) (nodeId : Int)
  | received (id : UInt64) (sender : Option String) (topic : Option String)
  deriving Repr

/-- Build a JSON object from fields. Lean's encoder owns string escaping. -/
def jsonObject (fields : List (String × Json)) : Json :=
  Json.obj (Std.TreeMap.Raw.ofList fields)

/-- Encode one event without a trailing line feed. -/
def recordLine (time : String) (event : RecordEvent) : String :=
  let base := [("time", Json.str time)]
  let fields := match event with
    | .peerId id nodeId =>
        base ++ [("msg", Json.str "PeerID"), ("id", Json.str id),
          ("node_id", Json.num ⟨nodeId, 0⟩)]
    | .received id sender topic =>
        let optional := (match sender with
          | some value => [("from", Json.str value)]
          | none => []) ++ (match topic with
          | some value => [("topic", Json.str value)]
          | none => [])
        base ++ [("msg", Json.str "Received Message"), ("id", Json.str (Nat.repr id.toNat))] ++ optional
  (jsonObject fields).compress

/-- Encode the start event with a peer id and node number. -/
def peerIdLine (time id : String) (nodeId : Int) : String :=
  recordLine time (.peerId id nodeId)

/-- Encode one received message event. -/
def receivedMessageLine (time : String) (id : UInt64) (sender topic : Option String) : String :=
  recordLine time (.received id sender topic)

end Libp2p.Protocols.Gossipsub.Interop
