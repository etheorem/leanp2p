import Libp2p.Protocols.ReqResp.Payload

/-!
# Req/resp: the reader core

The pure state machine that reads one req/resp stream (ARCHITECTURE
§3.3). The bytes of a stream arrive in pieces, so the reader is a
`step` over `Event.bytes` and `Event.eof`, and its `Action`s hand each
finished chunk out. The same core reads both sides:

* the responder reads one request: a payload, then the end of the
  stream ("Responding side", rule 2);
* the requester reads the response: zero or more chunks, each a result
  byte, the context bytes, and a payload, then the end of the stream.

## One payload

```
<length n: protobuf varint> <chunk>* until n bytes are out
```

The reader takes the framed chunks one at a time
(`framing_format.txt`). It reads a chunk header before the body, and it
checks the budget there: the framed bytes after the prefix never pass
`max_compressed_len(n)` ("SSZ-snappy encoding strategy": "A reader MUST
NOT read more than `max_compressed_len(n)` bytes"). So the buffer never
holds a body the reader would refuse (§5.1). The stream identifier comes
first, data chunks check their CRC-32C, padding and the skippable range
are skipped, and the unskippable range is an error. The payload ends at
the chunk that brings the output to exactly `n` bytes. A chunk that
overshoots is an error ("Any remaining bytes, after having read the `n`
SSZ bytes"). A payload of `n = 0` reads no chunk: go's snappy writer
writes none for an empty input (the fixture `empty` is the prefix
alone).

The decompression state that carries from chunk to chunk is the output
so far and the budget spent, in `Phase.frames`. Snappy blocks are
independent, so nothing else carries.

## Ends and errors

The end of the stream is an `Event.eof`. Between two chunks it answers
`Action.finished`, the orderly end of §3.5. Inside a chunk it is
`Error.truncated` ("An early EOF"). On the request side, a byte after
the request is `Error.trailingBytes` ("at which point an EOF should
arise"). On the response side, the reader stops after an error chunk
("only the last chunk is allowed to have a non-zero error code") and
after `maxChunks` chunks ("Requesting side", rules 1 and 4), and it
reads no byte after that, so the answer never depends on how the
transport split the reads. A protocol error ends the reader; the shell
resets the stream.

## Termination

`step` is total. `drain` advances until the buffer runs short, and each
advance either consumes a byte or moves to a phase that consumes one
next, so three advances per buffered byte, plus three, bound the loop.
The bound is the fuel of a structural recursion.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp.Core

open Libp2p.Protocols
open Libp2p.Protocols.ReqResp

/-- Which side of the exchange the reader serves. -/
inductive Side where
  /-- The responder reads the one request. -/
  | request
  /-- The requester reads the response chunks. -/
  | response
  deriving DecidableEq, Repr

/-- What the reader knows of the method. -/
structure Config where
  /-- The side the reader serves. -/
  side : Side
  /-- The bounds of a request payload, or of a success chunk. -/
  bounds : Bounds
  /-- The width of the context bytes of a success chunk. -/
  contextLen : Nat
  /-- The most chunks the requester reads. -/
  maxChunks : Nat
  deriving DecidableEq, Repr

/-- Where the reader stands. -/
inductive Phase where
  /-- Before the result byte of a response chunk. -/
  | result
  /-- Before the context bytes of a success chunk. -/
  | context (r : Result)
  /-- Before the length prefix. -/
  | length (r : Result) (ctx : ByteArray)
  /-- Inside the framed stream of `n` bytes: `out` so far, `used` framed
  bytes spent of the budget, and whether the identifier came. -/
  | frames (r : Result) (ctx : ByteArray) (n : Nat) (out : ByteArray) (used : Nat) (seen : Bool)
  /-- After the last payload. Only the end of the stream may follow. -/
  | ended
  deriving BEq

/-- The state of the reader. -/
structure State where
  /-- The method the reader reads. -/
  config : Config
  /-- Where the reader stands. -/
  phase : Phase
  /-- The bytes that arrived and are not consumed yet. -/
  buf : ByteArray
  /-- The chunks handed out so far. -/
  chunks : Nat
  deriving BEq

/-- What arrives from the stream. -/
inductive Event where
  /-- Bytes from one read. -/
  | bytes (b : ByteArray)
  /-- The peer closed its write direction. -/
  | eof
  deriving BEq

/-- What the shell does. -/
inductive Action where
  /-- Hand out one finished chunk (on the request side, the request). -/
  | chunk (c : Chunk)
  /-- The stream ended in order. -/
  | finished
  deriving BEq

/-! The bytes of these types are shown by size and as hex, since a
global `Repr ByteArray` would leak into every importer (PRINCIPLES 1.6). -/

/-- The hex of a byte array, for test output. -/
def hexOf (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length < 2 then "0" ++ s else s)

instance : Repr Chunk where
  reprPrec c _ := s!"⟨{repr c.result}, ctx {hexOf c.context}, {c.payload.size} bytes⟩"

instance : Repr Phase where
  reprPrec
    | .result, _ => "result"
    | .context r, _ => s!"context {repr r}"
    | .length r ctx, _ => s!"length {repr r} {hexOf ctx}"
    | .frames r _ n out used seen, _ => s!"frames {repr r} n={n} out={out.size} used={used} seen={seen}"
    | .ended, _ => "ended"

instance : Repr State where
  reprPrec s _ := s!"⟨{repr s.phase}, buf {s.buf.size}, chunks {s.chunks}⟩"

instance : Repr Event where
  reprPrec
    | .bytes b, _ => s!"bytes {hexOf b}"
    | .eof, _ => "eof"

instance : Repr Action where
  reprPrec
    | .chunk c, _ => s!"chunk {repr c}"
    | .finished, _ => "finished"

/-- The phase a reader starts in. A responder with no request content
expects the end at once, and a requester that asked for no chunk too. -/
def Config.start (c : Config) (hasRequest : Bool) : Phase :=
  match c.side with
  | .request => if hasRequest then .length .success ByteArray.empty else .ended
  | .response => if c.maxChunks = 0 then .ended else .result

/-- A fresh reader. -/
def init (c : Config) (hasRequest : Bool := true) : State :=
  ⟨c, c.start hasRequest, ByteArray.empty, 0⟩

/-! ## Reading pieces of the buffer -/

/-- The bytes after the first `k`. -/
def dropB (b : ByteArray) (k : Nat) : ByteArray := b.extract k b.size

/-- The length prefix at the front of `b`: `none` when more bytes may
complete it; else the value and the bytes it took. -/
def lengthB? (b : ByteArray) : Option (Except Error (Nat × Nat)) := Id.run do
  let mut v := 0
  for i in [0:Constants.lengthPrefixMaxBytes] do
    let some x := b[i]? | return none
    v := v + (x.toNat % 128) * 128 ^ i
    if x.toNat < 128 then
      return some (if v < 2 ^ 64 then .ok (v, i + 1) else .error .lengthPrefix)
  return some (.error .lengthPrefix)

/-- The little-endian `UInt32` of four bytes from `pos`. -/
def le32 (b : ByteArray) (pos : Nat) : UInt32 :=
  let byte (i : Nat) : UInt32 := (b.get! (pos + i)).toUInt32
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24)

/-- The data of one data chunk body, after its checksum check. `room` is
the count of bytes the payload still needs. -/
def dataOf (kind : SnappyFrame.Kind) (body : ByteArray) (room : Nat) : Except Error ByteArray := do
  if body.size < Constants.snappyCrcLen then throw (.frame .shortDataChunk)
  let stored := le32 body 0
  let raw := dropB body Constants.snappyCrcLen
  let cap := min Constants.snappyMaxDataLen room
  let data ← match kind with
    | .compressed =>
      match Mock.Snappy.decompress raw cap with
      | .ok d => pure d
      | .error .outputTooLarge =>
        -- The block announces more than the cap: past the payload, or
        -- past the 65536 bytes a chunk may carry.
        throw (if room < Constants.snappyMaxDataLen then .tooManyBytes else .frame .dataTooLong)
      | .error _ => throw (.frame .badBlock)
    | _ =>
      if Constants.snappyMaxDataLen < raw.size then throw (.frame .dataTooLong)
      if room < raw.size then throw .tooManyBytes
      pure raw
  if Crc32c.maskB (Crc32c.crc32cB data) ≠ stored then throw (.frame .badChecksum)
  return data

/-! ## One advance -/

/-- The phase after a finished chunk, the action, and the new count. -/
def finishChunk (s : State) (r : Result) (ctx out : ByteArray) : State × Action :=
  let chunks := s.chunks + 1
  let next : Phase :=
    match s.config.side, r with
    | .response, .success => if chunks < s.config.maxChunks then .result else .ended
    | _, _ => .ended
  ({ s with phase := next, chunks }, .chunk ⟨r, ctx, out⟩)

/-- The bounds a payload of result `r` must fit: the method's for a
success, `ErrorMessage` for an error chunk. -/
def boundsFor (c : Config) : Result → Bounds
  | .success => c.bounds
  | _ => Bounds.errorMessage

/-- Advance once over the buffer. `none` when the buffer holds too few
bytes for the next step. -/
def advance (s : State) : Except Error (Option (State × Option Action)) :=
  match s.phase with
  | .ended =>
    -- The requester stops reading after its last chunk, so the bytes
    -- after it are never its concern. The responder must see the end.
    if s.config.side = .response ∨ s.buf.size = 0 then .ok none else .error .trailingBytes
  | .result =>
    match s.buf[0]? with
    | none => .ok none
    | some x =>
      -- Every byte value is a result (`Result.ofCode?IsSome`); the `none`
      -- arm keeps the match total.
      match Result.ofCode? x.toNat with
      | none => .error .trailingBytes
      | some r =>
        let phase : Phase := if r = .success then .context r else .length r ByteArray.empty
        .ok (some ({ s with phase, buf := dropB s.buf 1 }, none))
  | .context r =>
    let k := s.config.contextLen
    if s.buf.size < k then .ok none
    else .ok (some ({ s with phase := .length r (s.buf.extract 0 k), buf := dropB s.buf k }, none))
  | .length r ctx =>
    match lengthB? s.buf with
    | none => .ok none
    | some (.error e) => .error e
    | some (.ok (n, k)) =>
      if !(boundsFor s.config r).admits n then .error (.lengthOutOfBounds n)
      else
        let s := { s with buf := dropB s.buf k }
        if n = 0 then
          let (s, a) := finishChunk s r ctx ByteArray.empty
          .ok (some (s, some a))
        else .ok (some ({ s with phase := .frames r ctx n ByteArray.empty 0 false }, none))
  | .frames r ctx n out used seen =>
    match SnappyFrame.decodeHeaderB? s.buf 0 with
    | none => .ok none
    | some (.error _) => .error (.frame .malformedHeader)
    | some (.ok (kind, len)) =>
      let spent := used + Constants.snappyHeaderLen + len
      -- The budget check comes before the body is buffered (§5.1).
      if Constants.maxCompressedLen n < spent then .error .overBudget
      else if s.buf.size < Constants.snappyHeaderLen + len then .ok none
      else
        let body := s.buf.extract Constants.snappyHeaderLen (Constants.snappyHeaderLen + len)
        let s := { s with buf := dropB s.buf (Constants.snappyHeaderLen + len) }
        let frames (out : ByteArray) (seen : Bool) : Phase := .frames r ctx n out spent seen
        match kind with
        | .streamId =>
          if body.toList.map (·.toNat) = Constants.snappyStreamBody then
            .ok (some ({ s with phase := frames out true }, none))
          else .error (.frame .badStreamId)
        | .unskippable c _ => .error (.frame (.unskippable c))
        | .padding | .skippable _ _ =>
          if seen then .ok (some ({ s with phase := frames out seen }, none))
          else .error (.frame .missingStreamId)
        | .compressed | .uncompressed =>
          if !seen then .error (.frame .missingStreamId)
          else
            match dataOf kind body (n - out.size) with
            | .error e => .error e
            | .ok data =>
              let out := out ++ data
              if out.size = n then
                let (s, a) := finishChunk s r ctx out
                .ok (some (s, some a))
              else .ok (some ({ s with phase := frames out seen }, none))

/-- Advance until the buffer runs short. `fuel` bounds the rounds; see
the module doc for why three per buffered byte, plus three, suffice. -/
def drain : Nat → State → List Action → Except Error (State × List Action)
  | 0, s, acts => .ok (s, acts.reverse)
  | fuel + 1, s, acts =>
    match advance s with
    | .error e => .error e
    | .ok none => .ok (s, acts.reverse)
    | .ok (some (s', a)) => drain fuel s' (match a with | some a => a :: acts | none => acts)

/-- The reader's transition. -/
def step (s : State) : Event → Except Error (State × List Action)
  | .bytes b =>
    let s := { s with buf := s.buf ++ b }
    drain (3 * s.buf.size + 3) s []
  | .eof =>
    match s.phase with
    | .ended =>
      if s.config.side = .request ∧ s.buf.size ≠ 0 then .error .trailingBytes
      else .ok (s, [.finished])
    | .result =>
      if s.buf.size = 0 then .ok ({ s with phase := .ended }, [.finished]) else .error .truncated
    | _ => .error .truncated

/-- Whether the reader has read all it reads: the requester after its
last chunk, the responder after the request. The responder still waits
for the end of the stream. -/
def State.done (s : State) : Bool := s.phase == .ended

/-! ## Facts of the core -/

/-- A responder that read the request refuses any byte that follows
("at which point an EOF should arise"). -/
theorem endedRefusesBytes (s : State) (b : ByteArray) (hp : s.phase = .ended)
    (hside : s.config.side = .request) (hb : 0 < b.size) :
    step s (.bytes b) = .error .trailingBytes := by
  -- The fuel is a successor, so `drain` takes one round.
  show drain (3 * (s.buf ++ b).size + 2 + 1) { s with buf := s.buf ++ b } [] = _
  -- `simp` states an empty append as two empty arrays; `b` is not empty.
  have hne : ¬(s.buf = ByteArray.empty ∧ b = ByteArray.empty) := by
    rintro ⟨_, rfl⟩
    simp at hb
  simp [drain, advance, hp, hside, hne]

/-- A requester that read no chunk sees the orderly end at an end of
stream: zero chunks is a valid response ("A `response` is formed by zero
or more `response_chunk`s"). -/
theorem eofBetweenChunks (s : State) (hp : s.phase = .result) (hb : s.buf.size = 0) :
    step s .eof = .ok ({ s with phase := .ended }, [.finished]) := by
  simp [step, hp, hb]

/-- An end of stream inside a payload is an early EOF, whatever is
buffered ("An early EOF, before fully reading the declared length-prefix
worth of SSZ bytes"). -/
theorem eofInsidePayload (s : State) (r : Result) (ctx out : ByteArray) (n used : Nat)
    (seen : Bool) (hp : s.phase = .frames r ctx n out used seen) :
    step s .eof = .error .truncated := by
  simp [step, hp]

end Libp2p.Protocols.ReqResp.Core
