import Bytes
import Varint
import Libp2p.Protocols.Gossipsub.Rpc

/-!
# Gossipsub payloads as `ByteArray`

The router core and the RPC codec work on the `List Nat` byte model,
which costs about 24 bytes of heap per payload byte: one 10 MiB message
through `Core.step` takes 3.3 s and peaks at 1.76 GB
(etheorem/leanp2p#110, item 8). The core never reads a payload, only its
id and its topic. So the node keeps each payload as a `ByteArray` and
hands the core a *handle* in its place: the message id's bytes, in the
`data` field.

* `splitInbound` walks a raw RPC once over the `ByteArray`. It copies
  every field as it is, except the `data` of each published message,
  which it lifts out, stores under its id, and replaces with the
  handle. The id comes from a `ByteArray` id function, so the payload
  never becomes a list. A payload with no id fails the split
  (`SplitError.noId`).
* `joinOutbound` encodes an RPC of handles with the model encoder. With
  handles in place of payloads, that RPC is small. Then `joinOutbound`
  appends each real payload as raw bytes. Protobuf takes fields in any
  order, so the `data` field goes last in its message.

`Tests/Gossipsub/Payload.lean` pins both against the model codec
(CLAUDE.md, "Proofs and tests", rule 2): the model decode of the split
RPC is the model decode of the original with handles for payloads, and
the model decode of the joined bytes is the original RPC.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Payload

/-- The field number of `RPC.publish`, and of `Message.data` and
`Message.topic` (`gossipsub-v1.0.md`, the protobuf). -/
def rpcPublish : Nat := 2
def msgData : Nat := 2
def msgTopic : Nat := 4

/-- A varint's bytes. -/
private def varintB (n : Nat) : ByteArray := Bytes.ofNatList (Varint.encodeNat n)

/-- A length-delimited field: its tag, its length, its bytes. -/
def lenField (num : Nat) (body : ByteArray) : ByteArray :=
  varintB (num * 8 + 2) ++ varintB body.size ++ body

/-- One field at `pos`: its number, wire type, the span of the whole
field, and for wire type 2 the span of its payload. `none` on a
malformed or truncated field. A length is checked against the input
before any slice, so the walk reads no byte past the end (ARCHITECTURE
§5.1). -/
private def fieldAt (b : ByteArray) (pos : Nat) :
    Option (Nat × Nat × Nat × Nat × Nat) := do
  let (tag, p1) ← (Varint.decodeAt? b pos).toOption
  let num := tag.val / 8
  let wire := tag.val % 8
  match wire with
  | 0 =>
    let (_, p2) ← (Varint.decodeAt? b p1).toOption
    return (num, wire, p2, p1, p1)
  | 1 => if p1 + 8 ≤ b.size then return (num, wire, p1 + 8, p1, p1) else none
  | 5 => if p1 + 4 ≤ b.size then return (num, wire, p1 + 4, p1, p1) else none
  | 2 =>
    let (len, p2) ← (Varint.decodeAt? b p1).toOption
    if p2 + len.val ≤ b.size then return (num, wire, p2 + len.val, p2, p2 + len.val) else none
  | _ => none

/-- Why a split fails. -/
inductive SplitError where
  /-- A field is malformed or truncated. The caller hands the core the
  original bytes, and the core's decoder reports the error. -/
  | malformed
  /-- The id function gave no id for a payload. -/
  | noId
  deriving DecidableEq, Repr

/-- Split one encoded `Message`: its bytes with the `data` field
replaced by `handle`, and the payload. `idOf` names the handle from the
topic and the payload. A message with no `data` keeps its bytes and
yields no payload. -/
private def splitMessage (b : ByteArray) (idOf : String → ByteArray → Option MessageId) :
    Except SplitError (ByteArray × Option (MessageId × ByteArray)) := Id.run do
  let mut pos := 0
  let mut kept : ByteArray := .empty
  let mut topic : Option String := none
  let mut data : Option ByteArray := none
  -- Each field moves `pos` forward, so the walk ends within `b.size` steps.
  for _ in [0:b.size + 1] do
    if pos ≥ b.size then break
    match fieldAt b pos with
    | none => return .error .malformed
    | some (num, wire, stop, start, payloadStop) =>
      if num == msgData && wire == 2 then
        data := some (b.extract start payloadStop)
      else
        if num == msgTopic && wire == 2 then
          topic := String.fromUTF8? (b.extract start payloadStop)
        kept := kept ++ b.extract pos stop
      pos := stop
  match data, topic with
  | some d, some t =>
    let some id := idOf t d | return .error .noId
    return .ok (kept ++ lenField msgData (Bytes.ofNatList id.bytes), some (id, d))
  | some _, none => return .error .malformed
  | none, _ => return .ok (b, none)

/-- Split a raw RPC: the RPC with handles for payloads, and the
payloads by id. The first failed message fails the whole split. -/
def splitInbound (b : ByteArray) (idOf : String → ByteArray → Option MessageId) :
    Except SplitError (ByteArray × List (MessageId × ByteArray)) := Id.run do
  let mut pos := 0
  let mut out : ByteArray := .empty
  let mut payloads : List (MessageId × ByteArray) := []
  for _ in [0:b.size + 1] do
    if pos ≥ b.size then break
    match fieldAt b pos with
    | none => return .error .malformed
    | some (num, wire, stop, start, payloadStop) =>
      if num == rpcPublish && wire == 2 then
        match splitMessage (b.extract start payloadStop) idOf with
        | .error e => return .error e
        | .ok (msg, p) =>
          out := out ++ lenField rpcPublish msg
          if let some e := p then payloads := e :: payloads
      else
        out := out ++ b.extract pos stop
      pos := stop
  return .ok (out, payloads.reverse)

/-- Encode an RPC whose messages carry handles, with each real payload
from `lookup`. The encoder leaves out a message whose payload is gone.
The answer is the RPC bytes, without the frame's length prefix. -/
def joinOutbound (r : Rpc.RPC) (lookup : MessageId → Option ByteArray) : ByteArray := Id.run do
  let mut out := Bytes.ofNatList (Pb.encodeMessage { r with publish := [] })
  for m in r.publish do
    let handle : MessageId := ⟨m.data.getD []⟩
    if let some payload := lookup handle then
      let inner := Bytes.ofNatList (Pb.encodeMessage { m with data := none })
      out := out ++ lenField rpcPublish (inner ++ lenField msgData payload)
  return out

end Libp2p.Protocols.Gossipsub.Payload
