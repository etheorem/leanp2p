import Bytes
import Varint
import Libp2p.Mux.Constants

/-!
# The mplex message codec

The wire format of `vendor/specs/mplex/README.md`, "Message format".
Every message is a header varint, a length varint, and `length` bytes
of data:

```
| header  | length  | data           |
| uvarint | uvarint | 'length' bytes |
```

The low three bits of the header are the flag. The other bits are the
stream id: `header = id * 8 + flag`. The header takes at most 9 bytes
(the unsigned-varint budget), so a stream id stays below `2 ^ 60`.

Two decoders read the same format. `decode?` is the model over the
`List Nat` byte model, and it carries the round-trip theorem.
`decodeAtB?` is the production decoder over `ByteArray`. It reads in
place from an offset, and the suite pins it to the model on every run
(CLAUDE.md, "Proofs and tests").

Both decoders answer the same three ways, through `Bytes.DecodeError`:

* `.ok` with the message and the rest of the input;
* `truncated`: the input ends inside the message, and more bytes can
  complete it. A header varint shorter than 9 bytes that is still open
  is this case;
* `malformed`: a protocol error. A varint that cannot end within 9
  bytes is this case, and no later byte can repair it. A flag of 7 and
  a declared length above `mplexMessageCap` are this case too.

The cap check comes straight after the length varint, before the
decoder waits for the data. A peer that declares 1 MiB + 1 bytes gets
its protocol error at once, and the session allocates nothing for it
(ARCHITECTURE §5.1).
-/

set_option autoImplicit false

namespace Libp2p.Mux.Mplex.Wire

open Bytes

/-! ## Flags -/

/-- The seven message flags of the spec, "Flag Values". The suffix
names the side of the stream that sends the message: `Initiator` for
the side that opened the stream, `Receiver` for the other side. -/
inductive Flag where
  /-- Open a stream. The data is the stream name. -/
  | newStream
  /-- Data from the receiver of the stream. -/
  | messageReceiver
  /-- Data from the initiator of the stream. -/
  | messageInitiator
  /-- The receiver closed its write direction. -/
  | closeReceiver
  /-- The initiator closed its write direction. -/
  | closeInitiator
  /-- The receiver reset the stream. -/
  | resetReceiver
  /-- The initiator reset the stream. -/
  | resetInitiator
  deriving DecidableEq, Repr

namespace Flag

/-- The wire code of a flag, 0 to 6. -/
def code : Flag → Nat
  | newStream => 0
  | messageReceiver => 1
  | messageInitiator => 2
  | closeReceiver => 3
  | closeInitiator => 4
  | resetReceiver => 5
  | resetInitiator => 6

/-- The flag of a wire code. Code 7 names no flag. -/
def ofCode? : Nat → Option Flag
  | 0 => some newStream
  | 1 => some messageReceiver
  | 2 => some messageInitiator
  | 3 => some closeReceiver
  | 4 => some closeInitiator
  | 5 => some resetReceiver
  | 6 => some resetInitiator
  | _ => none

theorem ofCodeCode (f : Flag) : ofCode? f.code = some f := by
  cases f <;> rfl

theorem codeLt (f : Flag) : f.code < 8 := by
  cases f <;> decide

end Flag

/-! ## The message model -/

/-- The first stream id outside the 9-byte header: `2 ^ 60`. -/
def idLimit : Nat := 2 ^ 60

/-- The header value: the id above the three flag bits. -/
def headerValue (flag : Flag) (id : Nat) : Nat :=
  id * 8 + flag.code

/-- One message over the byte model. -/
structure Message where
  /-- The flag. -/
  flag : Flag
  /-- The stream id. -/
  id : Nat
  /-- The data. -/
  payload : List Nat
  deriving DecidableEq, Repr

/-- The conditions under which a message has an encoding that decodes:
the id fits the header, the data fits the cap, and the data holds
bytes. -/
structure Message.Valid (m : Message) : Prop where
  /-- The id fits the 9-byte header. -/
  idLt : m.id < idLimit
  /-- The data fits the cap. -/
  lengthLe : m.payload.length ≤ Libp2p.Mux.mplexMessageCap
  /-- The data holds bytes. -/
  bytes : ∀ x ∈ m.payload, x < 256

/-- The encoding: the header varint, the length varint, the data. -/
def encode (m : Message) : List Nat :=
  Varint.encodeNat (headerValue m.flag m.id) ++ Varint.encodeNat m.payload.length ++ m.payload

/-- One message off the front of the input, and the rest of it. The
module doc lists the answers. -/
def decode? (l : List Nat) : Except DecodeError (Message × List Nat) := do
  let (header, afterHeader) ← Varint.decode? l
  let some flag := Flag.ofCode? (header.val % 8) | throw .malformed
  let (length, afterLength) ← Varint.decode? afterHeader
  -- The cap check comes before the data: no wait for a body over 1 MiB.
  if Libp2p.Mux.mplexMessageCap < length.val then throw .malformed
  let (payload, rest) ← take? length.val afterLength
  return ({ flag, id := header.val / 8, payload }, rest)

/-! ## The round trip -/

/-- A valid message decodes back from its encoding, with any rest
after it. A session decodes a message off the front of a buffer and
keeps the rest. -/
theorem decodeEncode (m : Message) (h : m.Valid) (rest : List Nat) :
    decode? (encode m ++ rest) = .ok (m, rest) := by
  -- The header fits 63 bits, so it is a `UVarint`.
  have hHeader : headerValue m.flag m.id < Varint.limit := by
    have := h.idLt
    have := Flag.codeLt m.flag
    simp only [headerValue, Varint.limit, Varint.maxBytes, idLimit] at *
    omega
  have hLength : m.payload.length < Varint.limit := by
    have := h.lengthLe
    simp only [Varint.limit, Varint.maxBytes, Libp2p.Mux.mplexMessageCap] at *
    omega
  -- `encodeNat` is the encoding of the `UVarint` that holds the value.
  have eHeader : Varint.encodeNat (headerValue m.flag m.id)
      = Varint.encode ⟨headerValue m.flag m.id, hHeader⟩ := rfl
  have eLength : Varint.encodeNat m.payload.length
      = Varint.encode ⟨m.payload.length, hLength⟩ := rfl
  have hFlag : (headerValue m.flag m.id) % 8 = m.flag.code := by
    have := Flag.codeLt m.flag
    simp only [headerValue]
    omega
  have hId : (headerValue m.flag m.id) / 8 = m.id := by
    have := Flag.codeLt m.flag
    simp only [headerValue]
    omega
  have hCap : ¬ Libp2p.Mux.mplexMessageCap < m.payload.length := by
    have := h.lengthLe
    omega
  simp only [decode?, encode, eHeader, eLength, List.append_assoc,
    Varint.decodeEncodeSuffix, hFlag, Flag.ofCodeCode, hCap, ↓reduceIte,
    take?Append rest h.bytes, hId, bind, Except.bind, pure, Except.pure]

/-- A declared length above the cap is a protocol error, whatever
follows it. The decoder answers before any data arrives. -/
theorem decodeOverCap (flag : Flag) (id : Nat) (hId : id < idLimit) (rest : List Nat) :
    decode? (Varint.encodeNat (headerValue flag id)
      ++ Varint.encodeNat (Libp2p.Mux.mplexMessageCap + 1) ++ rest) = .error .malformed := by
  have hHeader : headerValue flag id < Varint.limit := by
    have := Flag.codeLt flag
    simp only [headerValue, Varint.limit, Varint.maxBytes, idLimit] at *
    omega
  have hLength : Libp2p.Mux.mplexMessageCap + 1 < Varint.limit := by
    simp only [Varint.limit, Varint.maxBytes, Libp2p.Mux.mplexMessageCap]
    omega
  have eHeader : Varint.encodeNat (headerValue flag id)
      = Varint.encode ⟨headerValue flag id, hHeader⟩ := rfl
  have eLength : Varint.encodeNat (Libp2p.Mux.mplexMessageCap + 1)
      = Varint.encode ⟨Libp2p.Mux.mplexMessageCap + 1, hLength⟩ := rfl
  have hFlag : (headerValue flag id) % 8 = flag.code := by
    have := Flag.codeLt flag
    simp only [headerValue]
    omega
  have hCap : Libp2p.Mux.mplexMessageCap < Libp2p.Mux.mplexMessageCap + 1 := by omega
  simp only [decode?, eHeader, eLength, List.append_assoc, Varint.decodeEncodeSuffix,
    hFlag, Flag.ofCodeCode, hCap, ↓reduceIte, bind, Except.bind]
  rfl

/-- Nine continuation bytes are a protocol error, with no more input. -/
example : decode? (List.replicate 9 0x80) = .error .malformed := rfl

/-- Five continuation bytes are a short prefix: more input can end the
varint. -/
example : decode? (List.replicate 5 0x80) = .error .truncated := rfl

/-- A header with flag code 7 is a protocol error. -/
example : decode? [7, 0] = .error .malformed := rfl

/-- NewStream for stream 5 named `demo`: header `5 * 8 + 0 = 40`. -/
example : encode { flag := .newStream, id := 5, payload := [100, 101, 109, 111] }
    = [40, 4, 100, 101, 109, 111] := by
  simp [encode, headerValue, Flag.code, Varint.encodeNat]

/-! ## The wire form -/

/-- One message on the wire: the data is a `ByteArray`. -/
structure Frame where
  /-- The flag. -/
  flag : Flag
  /-- The stream id. -/
  id : Nat
  /-- The data. -/
  payload : ByteArray

/-- The model message of a frame. -/
def Frame.toMessage (f : Frame) : Message :=
  { flag := f.flag, id := f.id, payload := toNatList f.payload }

/-- The wire bytes of a message: `encode` over `ByteArray`. -/
def encodeB (flag : Flag) (id : Nat) (payload : ByteArray) : ByteArray :=
  ofNatList (Varint.encodeNat (headerValue flag id))
    ++ ofNatList (Varint.encodeNat payload.size) ++ payload

/-- One varint at offset `pos`, and the offset after it. The decoder
reads a copy of at most `Varint.maxBytes` bytes, so a long buffer costs
nothing extra. -/
def varintAt? (b : ByteArray) (pos : Nat) : Except DecodeError (Varint.UVarint × Nat) :=
  match Varint.decodeB? (b.extract pos (pos + Varint.maxBytes)) with
  | .ok (v, n) => .ok (v, pos + n)
  | .error e => .error e

/-- One message at offset `pos` of `b`, and the offset after it. The
answers are the answers of `decode?`. The decoder copies the data only
after the cap check, and only once all of it has arrived. -/
def decodeAtB? (b : ByteArray) (pos : Nat) : Except DecodeError (Frame × Nat) := do
  let (header, afterHeader) ← varintAt? b pos
  let some flag := Flag.ofCode? (header.val % 8) | throw .malformed
  let (length, afterLength) ← varintAt? b afterHeader
  if Libp2p.Mux.mplexMessageCap < length.val then throw .malformed
  let (payload, next) ← sliceAt? b afterLength length.val
  return ({ flag, id := header.val / 8, payload }, next)

end Libp2p.Mux.Mplex.Wire
