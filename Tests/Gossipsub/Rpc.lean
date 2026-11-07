import Tests.Support
import Libp2p.Protocols.Gossipsub.Rpc

/-!
# Gossipsub suite: the RPC codec

The wire messages of gossipsub v1.1, checked in both directions from the
field tables of the vendored spec, plus the strictness and rejection
cases and the length-delimited frame step.

The repository carries no gossipsub vector file (`PLAN`, "Vector
stance"). Fixed message bytes close the codec family. Each expected byte
string below carries a comment that derives it from the field numbers.

A field tag is `field number * 8 + wire type`. The wire types here are 0
for a varint and 2 for a byte string. A byte string tag is followed by
its length and then its bytes.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Rpc

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Rpc

/-! ## Fixed message samples -/

/-- A subscription of `foo`. -/
private def subFoo : SubOpts := { subscribe := true, topicid := "foo" }

/-- A message on topic `t` with no optional field. -/
private def msgT : Message :=
  { «from» := none, data := none, seqno := none, topic := ⟨"t"⟩, signature := none, key := none }

/-- A message with every field of the spec. -/
private def fullMsg : Message :=
  { «from» := some [1], data := some [2], seqno := some [3], topic := ⟨"t"⟩,
    signature := some [4], key := some [5] }

/-- A peer with the id bytes `[1, 2]` and no signed record. -/
private def peer12 : PeerInfo := { peerId := some [1, 2], signedPeerRecord := none }

/-- A prune of `g` with one peer and a backoff of 60 seconds. -/
private def pruneG : ControlPrune := { topicId := "g", peers := [peer12], backoff := some 60 }

/-- A control envelope with one prune. -/
private def controlPrune : ControlMessage :=
  { ihave := [], iwant := [], graft := [], prune := [pruneG] }

/-- An RPC with one subscription and one published message. -/
private def rpcSubPublish : RPC :=
  { subscriptions := [subFoo], publish := [msgT], control := none }

/-- An RPC with one control envelope. -/
private def rpcControl : RPC :=
  { subscriptions := [], publish := [], control := some controlPrune }

/-- An IHAVE of topic `t` with two message ids. -/
private def ihaveT : ControlIHave :=
  { topicId := "t", messageIds := [⟨[1]⟩, ⟨[2, 3]⟩] }

/-! ## Check helpers -/

/-- The model decode returns the expected value and consumes all bytes. -/
private def decodesAs {α : Type} [Pb.ProtoMessage α] [BEq α] (bs : List Nat) (want : α) : Bool :=
  match Pb.decodeMessage? (α := α) bs with
  | .ok (v, []) => v == want
  | _ => false

/-- The value encodes to the expected bytes. -/
private def encodesAs {α : Type} [Pb.ProtoMessage α] [BEq α] (v : α) (bs : List Nat) : Bool :=
  Pb.encodeMessage v == bs

/-- The model decode fails with the expected error. -/
private def rejectsWith {α : Type} [Pb.ProtoMessage α] (bs : List Nat) (e : Pb.Error) : Bool :=
  match Pb.decodeMessage? (α := α) bs with
  | .error e' => e' == e
  | .ok _ => false

/-- The model decode succeeds, whatever the value. -/
private def accepts {α : Type} [Pb.ProtoMessage α] (bs : List Nat) : Bool :=
  match Pb.decodeMessage? (α := α) bs with
  | .ok _ => true
  | .error _ => false

/-- The production decoder agrees with the model decoder on value, rest,
and consumed count. -/
private def productionAgrees {α : Type} [Pb.ProtoMessage α] [BEq α] (bs : List Nat) : Bool :=
  match Pb.decodeMessage? (α := α) bs, Pb.decodeMessageB? (α := α) (Bytes.ofNatList bs) with
  | .ok (v, rest), .ok (w, used) => v == w && rest == [] && used == bs.length
  | .error e, .error e' => e == e'
  | _, _ => false

/-- The frame step returns one payload and the rest after it. -/
private def frameIs (bytes payload rest : List Nat) : Bool :=
  match decodeFrame? bytes with
  | .ok (some (p, r)) => p == payload && r == rest
  | _ => false

/-- The frame step needs more bytes. -/
private def frameNeedsMore (bytes : List Nat) : Bool :=
  match decodeFrame? bytes with
  | .ok none => true
  | _ => false

/-- The frame step fails with the expected error. -/
private def frameFails (bytes : List Nat) (e : Pb.Error) : Bool :=
  match decodeFrame? bytes with
  | .error e' => e' == e
  | _ => false

/-! ## Order samples -/

private def subA : SubOpts := { subscribe := false, topicid := "a" }
private def subB : SubOpts := { subscribe := true, topicid := "b" }

private def msgA : Message :=
  { «from» := none, data := some [7], seqno := none, topic := ⟨"x"⟩, signature := none, key := none }

private def msgB : Message :=
  { «from» := some [8], data := none, seqno := none, topic := ⟨"y"⟩, signature := none, key := none }

private def peerA : PeerInfo := { peerId := some [1], signedPeerRecord := none }

private def peerB : PeerInfo := { peerId := some [2], signedPeerRecord := some [9] }

/-- The subscriptions of a decoded RPC, when the decode succeeds. -/
private def rpcSubscriptions (bs : List Nat) : Option (List SubOpts) :=
  match Pb.decodeMessage? (α := RPC) bs with
  | .ok (r, []) => some r.subscriptions
  | _ => none

/-- The published messages of a decoded RPC, when the decode succeeds. -/
private def rpcPublish (bs : List Nat) : Option (List Message) :=
  match Pb.decodeMessage? (α := RPC) bs with
  | .ok (r, []) => some r.publish
  | _ => none

/-- The message ids of a decoded IHAVE, when the decode succeeds. -/
private def ihaveIds (bs : List Nat) : Option (List MessageId) :=
  match Pb.decodeMessage? (α := ControlIHave) bs with
  | .ok (i, []) => some i.messageIds
  | _ => none

/-- The message ids of a decoded IWANT, when the decode succeeds. -/
private def iwantIds (bs : List Nat) : Option (List MessageId) :=
  match Pb.decodeMessage? (α := ControlIWant) bs with
  | .ok (i, []) => some i.messageIds
  | _ => none

/-- The peers of a decoded PRUNE, when the decode succeeds. -/
private def prunePeers (bs : List Nat) : Option (List PeerInfo) :=
  match Pb.decodeMessage? (α := ControlPrune) bs with
  | .ok (p, []) => some p.peers
  | _ => none

/-- Run the checks of this module. -/
def run (r : Runner) : IO Unit := do
  r.section "gossipsub Rpc"
    "vendor/specs/pubsub (README, gossipsub-v1.0.md, gossipsub-v1.1.md)"

  -- SubOpts: field 1 varint tag is 8, value 1 is true; field 2 bytes tag
  -- is 18, length 3, and "foo" is [102, 111, 111].
  r.check "spec SubOpts subscribe foo decodes"
    (decodesAs (α := SubOpts) [8, 1, 18, 3, 102, 111, 111] subFoo)
  r.check "spec SubOpts subscribe foo encodes byte-exact"
    (encodesAs subFoo [8, 1, 18, 3, 102, 111, 111])

  -- Message: field 4 bytes tag is 34, length 1, and "t" is 116.
  r.check "spec Message topic t decodes"
    (decodesAs (α := Message) [34, 1, 116] msgT)
  r.check "spec Message topic t encodes byte-exact"
    (encodesAs msgT [34, 1, 116])

  -- Full Message: field 1 tag 10, field 2 tag 18, field 3 tag 26, field 4
  -- tag 34, field 5 tag 42, field 6 tag 50. Each payload has length 1.
  r.check "spec full Message decodes"
    (decodesAs (α := Message)
      [10, 1, 1, 18, 1, 2, 26, 1, 3, 34, 1, 116, 42, 1, 4, 50, 1, 5] fullMsg)
  r.check "spec full Message encodes byte-exact"
    (encodesAs fullMsg [10, 1, 1, 18, 1, 2, 26, 1, 3, 34, 1, 116, 42, 1, 4, 50, 1, 5])

  -- RPC: field 1 bytes tag is 10, the SubOpts payload has length 7;
  -- field 2 bytes tag is 18, the Message payload has length 3.
  r.check "spec RPC subscription and publish decodes"
    (decodesAs (α := RPC)
      [10, 7, 8, 1, 18, 3, 102, 111, 111, 18, 3, 34, 1, 116] rpcSubPublish)
  r.check "spec RPC subscription and publish encodes byte-exact"
    (encodesAs rpcSubPublish [10, 7, 8, 1, 18, 3, 102, 111, 111, 18, 3, 34, 1, 116])

  -- ControlPrune: field 1 tag 10, field 2 bytes tag 18 with the PeerInfo
  -- payload [10, 2, 1, 2], field 3 varint tag is 24, value 60.
  r.check "spec ControlPrune topic peers backoff decodes"
    (decodesAs (α := ControlPrune) [10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60] pruneG)
  r.check "spec ControlPrune topic peers backoff encodes byte-exact"
    (encodesAs pruneG [10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60])

  -- ControlMessage: field 4 bytes tag is 34, the ControlPrune payload has
  -- length 11.
  r.check "spec ControlMessage with prune decodes"
    (decodesAs (α := ControlMessage)
      [34, 11, 10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60] controlPrune)
  r.check "spec ControlMessage with prune encodes byte-exact"
    (encodesAs controlPrune [34, 11, 10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60])

  -- RPC: field 3 bytes tag is 26, the ControlMessage payload has length 13.
  r.check "spec RPC with control decodes"
    (decodesAs (α := RPC)
      [26, 13, 34, 11, 10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60] rpcControl)
  r.check "spec RPC with control encodes byte-exact"
    (encodesAs rpcControl [26, 13, 34, 11, 10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60])

  -- ControlIHave: field 1 tag 10 with "t"; field 2 bytes tag 18 twice, the
  -- payloads [1] and [2, 3].
  r.check "spec ControlIHave topic and ids decodes"
    (decodesAs (α := ControlIHave) [10, 1, 116, 18, 1, 1, 18, 2, 2, 3] ihaveT)
  r.check "spec ControlIHave topic and ids encodes byte-exact"
    (encodesAs ihaveT [10, 1, 116, 18, 1, 1, 18, 2, 2, 3])

  -- The production decoder and the model decoder agree on the fixed bytes.
  r.check "spec RPC production path agrees with the model"
    (productionAgrees (α := RPC)
      [26, 13, 34, 11, 10, 1, 103, 18, 4, 10, 2, 1, 2, 24, 60])

  -- Strictness: a bool above 1, a wrong wire type on a singular field,
  -- and invalid UTF-8 are badField.
  r.check "SubOpts subscribe varint 2 rejected as badField"
    (rejectsWith (α := SubOpts) [8, 2] .badField)
  -- Field 1 with the bytes wire type: tag is 10, length 1, payload 5.
  r.check "SubOpts subscribe bytes wire type rejected as badField"
    (rejectsWith (α := SubOpts) [10, 1, 5] .badField)
  -- Field 2 bytes with the payload [255], which has no UTF-8 reading.
  r.check "SubOpts topicid invalid UTF-8 rejected as badField"
    (rejectsWith (α := SubOpts) [18, 1, 255] .badField)
  -- Field 2 with the varint wire type: tag is 16.
  r.check "SubOpts topicid varint wire type rejected as badField"
    (rejectsWith (α := SubOpts) [16, 1] .badField)

  -- The required topic. An empty buffer has no field 4.
  r.check "Message without topic rejected as badField"
    (rejectsWith (α := Message) [] .badField)
  r.check "Message topic invalid UTF-8 rejected as badField"
    (rejectsWith (α := Message) [34, 1, 255] .badField)
  -- A valid topic, then field 2 with the varint wire type (tag 16).
  r.check "Message data varint wire type rejected as badField"
    (rejectsWith (α := Message) [34, 1, 116, 16, 1] .badField)

  -- Field 3 with the bytes wire type: tag is 26, length 1, payload 5.
  r.check "ControlPrune backoff bytes wire type rejected as badField"
    (rejectsWith (α := ControlPrune) [10, 1, 103, 26, 1, 5] .badField)
  -- The varint of 2^63 is ten groups, one more than the nine-byte budget.
  -- The varint decoder rejects it as malformed before the table runs.
  r.check "ControlPrune backoff value 2^63 rejected as malformed"
    (rejectsWith (α := ControlPrune)
      [10, 1, 103, 24, 128, 128, 128, 128, 128, 128, 128, 128, 128, 1]
      (.framing .malformed))

  -- A control payload whose nested ControlPrune payload is the byte 5,
  -- which is an invalid tag: field 0 is not a legal number.
  r.check "RPC control payload that is not a ControlMessage rejected"
    (rejectsWith (α := RPC) [26, 3, 34, 1, 5] .badField)
  -- A publish payload with no topic fails the Message table.
  r.check "RPC publish payload that is not a Message rejected"
    (rejectsWith (α := RPC) [18, 0] .badField)

  -- A repeated field of another wire type is skipped. Field 1 varint tag
  -- is 8, value 1.
  r.check "RPC subscriptions entry with varint wire type skipped, decode succeeds"
    (decodesAs (α := RPC) [8, 1] { subscriptions := [], publish := [], control := none })

  -- Field 5 of ControlMessage (`idontwant` in v1.2) is out of scope. Bytes
  -- tag is 42, length 1, payload 1. The value drops the field, and the
  -- re-encode omits it.
  r.check "ControlMessage idontwant field 5 ignored and dropped on re-encode"
    (decodesAs (α := ControlMessage) [42, 1, 1]
        { ihave := [], iwant := [], graft := [], prune := [] } &&
      Pb.encodeMessage ({ ihave := [], iwant := [], graft := [], prune := [] } : ControlMessage) == [])

  -- Field 99 bytes: tag 794 is [154, 6], length 1, payload 2. The value
  -- drops the field, and the re-encode omits it.
  r.check "RPC unknown field 99 ignored, structure drops it"
    (decodesAs (α := RPC) [154, 6, 1, 2]
        { subscriptions := [], publish := [], control := none } &&
      Pb.encodeMessage ({ subscriptions := [], publish := [], control := none } : RPC) == [])

  -- The frame step. The length prefix of 1048577 is over the cap, so the
  -- decode stops before the body.
  r.check "frame length over rpcCap malformed before the body"
    (frameFails (Streams.Framing.encodeLength .uvarint 1048577 ++ [1, 2, 3])
      (.framing .malformed))
  -- The byte 128 is a varint continuation with no next byte.
  r.check "frame prefix cut short returns none" (frameNeedsMore [128])
  -- A zero-length frame is a legal empty RPC here. Identify rejects it
  -- (`Identify.Err.emptyFrame`, the spike's read rule); gossipsub has no
  -- such rule, because the empty RPC is a legal value.
  r.check "zero-length frame decodes to the empty RPC"
    (frameIs (Streams.Framing.encodeLength .uvarint 0) [] [])
  -- One frame of a fixed RPC, then the frame step reads its payload back.
  r.check "frame round trip: encodeFrame? then decodeFrame? returns the payload"
    (match encodeFrame? rpcControl with
     | some frame => frameIs frame (Pb.encodeMessage rpcControl) []
     | none => false)
  r.check "rpcCap constant is 1048576" (Constants.rpcCap == 1048576)

  -- Repeated fields keep their order.
  r.check "subscriptions keep their order through the round trip"
    (rpcSubscriptions (Pb.encodeMessage
        ({ subscriptions := [subA, subB], publish := [], control := none } : RPC)) ==
      some [subA, subB])
  r.check "publish keeps their order through the round trip"
    (rpcPublish (Pb.encodeMessage
        ({ subscriptions := [], publish := [msgA, msgB], control := none } : RPC)) ==
      some [msgA, msgB])
  r.check "message ids keep their order through the round trip"
    (ihaveIds (Pb.encodeMessage
        ({ topicId := "o", messageIds := [⟨[1]⟩, ⟨[2]⟩] } : ControlIHave)) ==
      some [⟨[1]⟩, ⟨[2]⟩] &&
      iwantIds (Pb.encodeMessage
        ({ messageIds := [⟨[3]⟩, ⟨[4]⟩] } : ControlIWant)) == some [⟨[3]⟩, ⟨[4]⟩])
  r.check "prune peers keep their order through the round trip"
    (prunePeers (Pb.encodeMessage
        ({ topicId := "p", peers := [peerA, peerB], backoff := none } : ControlPrune)) ==
      some [peerA, peerB])

end Tests.Gossipsub.Rpc
