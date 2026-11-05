import Varint
import Snappy
import Libp2p.Protocols.ReqResp.Crc32c
import Libp2p.Protocols.ReqResp.SnappyFrame

/-!
# Req/resp: the payload layer

The `ssz_snappy` encoding of one payload (phase0 `p2p-interface.md`,
"SSZ-snappy encoding strategy"):

```
payload ::= <length: protobuf varint of the raw byte count n> <framed snappy stream of the n bytes>
```

A request is one payload. A response chunk is a result byte, the
context bytes of altair (empty on an error result), then one payload
(altair `p2p-interface.md`, "Req-Resp interaction"). This module holds
the parts that both directions share:

* `Error`, the protocol error of req/resp (ARCHITECTURE §3.5), and
  `Result`, the closed set of result codes (§3.4).
* `Bounds` and `Limits`: the size bounds of the SSZ type, which the
  client project knows and passes in, since SSZ stays with the client
  (§8).
* The length prefix: `encodeLength` and `decodeLength?` over the byte
  model, with the round-trip theorem.
* The writer: `encodeFramesB` turns a payload into a framed stream, and
  `encodeRequestB` and `encodeChunkB` add the headers.

The reader is a state machine, since the bytes of one payload arrive in
pieces; `ReqResp/Core.lean` holds it.

## The length prefix

The spec asks for a protobuf varint: at most 10 bytes, decoded into the
full `Uint64` range. It SHOULD be minimal. So the writer is minimal, and
it shares `Varint.encodeNat` with the multiformats varint, whose minimal
bytes are the same. The reader accepts a non-minimal prefix of at most
10 bytes, since the spec makes minimality a SHOULD of the writer; the
multiformats decoder of `codec/varint` refuses both, so this module has
its own. Prysm reads the same way
(`vendor/prysm/beacon-chain/p2p/encoder/varint.go`, `readVarint`: up
to 10 bytes, then `proto.DecodeVarint`).
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp

open Libp2p.Protocols
open Bytes

/-! ## Errors and result codes -/

/-- What broke in a framed snappy stream (`framing_format.txt`). -/
inductive FrameError where
  /-- The first chunk is not the stream identifier (section 4.1). -/
  | missingStreamId
  /-- A stream identifier chunk with a body other than `sNaPpY`. -/
  | badStreamId
  /-- A chunk of the reserved unskippable range (section 4.5). -/
  | unskippable (code : Nat)
  /-- A data chunk shorter than its 4-byte checksum. -/
  | shortDataChunk
  /-- A data chunk with more than 65536 uncompressed bytes (4.2, 4.3). -/
  | dataTooLong
  /-- The masked CRC-32C does not match the data (section 3). -/
  | badChecksum
  /-- The block inside a compressed chunk is no snappy block. -/
  | badBlock
  /-- A header byte that is no byte, on the model path. -/
  | malformedHeader
  deriving DecidableEq, Repr, BEq

/-- The protocol error of req/resp. Each arm is a reason to reset the
stream (phase0 "Req/Resp interaction": "if not, they SHOULD reset the
stream immediately"). -/
inductive Error where
  /-- The length prefix runs past 10 bytes, or past `2 ^ 64 - 1`. -/
  | lengthPrefix
  /-- The length is outside the bounds of the type or `MAX_PAYLOAD_SIZE`. -/
  | lengthOutOfBounds (n : Nat)
  /-- The framed stream is broken. -/
  | frame (e : FrameError)
  /-- More framed bytes than `max_compressed_len(n)`. -/
  | overBudget
  /-- The frames hold more than the `n` bytes the prefix announced. -/
  | tooManyBytes
  /-- The stream ended inside a chunk (an early EOF). -/
  | truncated
  /-- Bytes after the end: after the request, after an error chunk, or
  after the last chunk the client asked for. -/
  | trailingBytes
  /-- The writer was handed a payload outside its bounds. -/
  | payloadOutOfBounds (n : Nat)
  /-- The stream failed underneath. -/
  | stream (e : Streams.Error)
  /-- The exchange ran past its deadline. -/
  | timeout
  /-- `MAX_CONCURRENT_REQUESTS` requests with this id are open toward
  the peer, so the spec forbids one more. -/
  | tooManyRequests
  /-- The host could not open the stream or negotiate the id. -/
  | openFailed (e : Mock.Core.Error)
  deriving DecidableEq, Repr, BEq

/-- The `result` byte of a response chunk (phase0 "Responding side"). -/
inductive Result where
  /-- `0`: a payload of the expected schema follows. -/
  | success
  /-- `1`: the request was invalid. -/
  | invalidRequest
  /-- `2`: the responder failed. -/
  | serverError
  /-- `3`: the responder lacks the resource. -/
  | resourceUnavailable
  /-- `4` to `127`: reserved, and an error when not recognized. -/
  | reserved (code : Nat) (h : 4 ≤ code ∧ code ≤ 127)
  /-- `128` to `255`: request-specific errors. -/
  | custom (code : Nat) (h : 128 ≤ code ∧ code ≤ 255)
  deriving DecidableEq, Repr

/-- The byte of a result. -/
def Result.toCode : Result → Nat
  | .success => Constants.resultSuccess
  | .invalidRequest => Constants.resultInvalidRequest
  | .serverError => Constants.resultServerError
  | .resourceUnavailable => Constants.resultResourceUnavailable
  | .reserved c _ => c
  | .custom c _ => c

/-- The result of a byte. Every byte value is a result. -/
def Result.ofCode? (c : Nat) : Option Result :=
  if c = Constants.resultSuccess then some .success
  else if c = Constants.resultInvalidRequest then some .invalidRequest
  else if c = Constants.resultServerError then some .serverError
  else if c = Constants.resultResourceUnavailable then some .resourceUnavailable
  else if h : 4 ≤ c ∧ c ≤ 127 then some (.reserved c h)
  else if h : 128 ≤ c ∧ c ≤ 255 then some (.custom c h)
  else none

/-- The result table is a bijection on the byte values (§3.4). -/
theorem Result.ofCode?_toCode (r : Result) : Result.ofCode? r.toCode = some r := by
  cases r with
  | reserved c h =>
    simp only [toCode, ofCode?, Constants.resultSuccess, Constants.resultInvalidRequest,
      Constants.resultServerError, Constants.resultResourceUnavailable]
    simp [show c ≠ 0 by omega, show c ≠ 1 by omega, show c ≠ 2 by omega,
      show c ≠ 3 by omega, h]
  | custom c h =>
    simp only [toCode, ofCode?, Constants.resultSuccess, Constants.resultInvalidRequest,
      Constants.resultServerError, Constants.resultResourceUnavailable]
    simp [show c ≠ 0 by omega, show c ≠ 1 by omega, show c ≠ 2 by omega,
      show c ≠ 3 by omega, show ¬(4 ≤ c ∧ c ≤ 127) by omega, h]
  | _ => decide

/-- Every byte value is a result: the six arms cover 0 to 255. -/
theorem Result.ofCode?IsSome (c : Nat) (h : c < 256) : (Result.ofCode? c).isSome := by
  unfold ofCode?
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  simp only [Constants.resultSuccess, Constants.resultInvalidRequest,
    Constants.resultServerError, Constants.resultResourceUnavailable] at *
  omega

/-- One response chunk, or one request when `result` is `success` and
`context` is empty. -/
structure Chunk where
  /-- The result code. -/
  result : Result
  /-- The context bytes: the `ForkDigest` of altair, or empty. -/
  context : ByteArray
  /-- The raw payload: the SSZ bytes of the client, or an
  `ErrorMessage` on an error result. -/
  payload : ByteArray
  deriving BEq

/-! ## Bounds -/

/-- The size bounds of one SSZ type, from the client project ("SSZ-snappy
encoding strategy": "within the expected size bounds derived from the
payload SSZ type"). -/
structure Bounds where
  /-- The least size of the type. -/
  minLen : Nat
  /-- The largest size of the type. -/
  maxLen : Nat
  deriving DecidableEq, Repr

/-- The bounds of an `ErrorMessage`, the payload of every error chunk. -/
def Bounds.errorMessage : Bounds := ⟨0, Constants.errorMessageLimit⟩

/-- Whether a length fits the bounds and `MAX_PAYLOAD_SIZE`, whichever
is smaller. -/
def Bounds.admits (b : Bounds) (n : Nat) : Bool :=
  b.minLen ≤ n && n ≤ b.maxLen && n ≤ Constants.maxPayloadSize

/-- One req/resp method, as the client project declares it. The
package frames the bytes; the method says how many. -/
structure Method where
  /-- The protocol id, from `Constants.reqRespId`. -/
  id : Mock.Core.ProtocolId
  /-- The bounds of the request payload. `none` for a method with "No
  Request Content" (GetMetaData): the request stream carries no byte. -/
  request : Option Bounds
  /-- The bounds of the payload of a success chunk. -/
  response : Bounds
  /-- The width of the context bytes of a success chunk: `0`, or
  `Constants.forkDigestLen` for a method with a `ForkDigest` context. -/
  contextLen : Nat
  /-- The most chunks the client reads ("Requesting side", rule 4). -/
  maxChunks : Nat

/-! ## The length prefix over the byte model -/

/-- The length prefix of `n`: minimal LEB128, which a protobuf varint
and a multiformats varint spell alike. -/
def encodeLength (n : Nat) : List Nat := Varint.encodeNat n

/-- The groups from byte `i` on. A byte at `i = 9` must end the value. A
zero after a continuation is accepted, since minimality is a SHOULD. -/
def lengthGroups (i : Nat) : List Nat → Except DecodeError (Nat × List Nat)
  | [] => .error .truncated
  | b :: rest =>
    if 256 ≤ b then .error .malformed
    else if b < 128 then .ok (b, rest)
    else if Constants.lengthPrefixMaxBytes ≤ i + 1 then .error .malformed
    else (lengthGroups (i + 1) rest).map fun (v, r) => (b - 128 + 128 * v, r)

/-- The length prefix at the front of the input, and the rest. A value
of `2 ^ 64` or more is malformed: ten bytes carry 70 bits, and the spec
reads into a `Uint64`. -/
def decodeLength? (l : List Nat) : Except DecodeError (Nat × List Nat) := do
  let (n, rest) ← lengthGroups 0 l
  if n < 2 ^ 64 then return (n, rest) else throw .malformed

/-- The groups read back what `encodeLength` wrote, when the value fits
the bytes left in the budget. -/
theorem lengthGroupsEncode (n i : Nat) (rest : List Nat)
    (h : n < 128 ^ (Constants.lengthPrefixMaxBytes - i)) (hi : i < Constants.lengthPrefixMaxBytes) :
    lengthGroups i (encodeLength n ++ rest) = .ok (n, rest) := by
  induction n using Nat.strongRecOn generalizing i with
  | _ n ih =>
    unfold encodeLength
    rw [Varint.encodeNat]
    split
    · next hlt =>
      have hb : ¬(256 ≤ n) := by omega
      simp only [List.singleton_append, lengthGroups, hb, hlt, ↓reduceIte]
    · next hn =>
      simp only [List.cons_append, lengthGroups]
      have hb : ¬(256 ≤ n % 128 + 128) := by omega
      have hc : ¬(n % 128 + 128 < 128) := by omega
      -- The value needs a second group, so the budget has room for it.
      have hroom : ¬(Constants.lengthPrefixMaxBytes ≤ i + 1) := by
        intro hle
        have : Constants.lengthPrefixMaxBytes - i = 1 := by omega
        rw [this] at h
        omega
      simp only [hb, hc, hroom, ↓reduceIte]
      have hdiv : n / 128 < 128 ^ (Constants.lengthPrefixMaxBytes - (i + 1)) := by
        have hk : Constants.lengthPrefixMaxBytes - i =
            (Constants.lengthPrefixMaxBytes - (i + 1)) + 1 := by omega
        rw [hk, Nat.pow_succ] at h
        omega
      have := ih (n / 128) (by omega) (i + 1) hdiv (by omega)
      unfold encodeLength at this
      rw [this]
      simp only [Except.map]
      congr 2
      omega

/-- The length prefix round-trips for every `Uint64` value. -/
theorem decodeLengthEncode (n : Nat) (rest : List Nat) (h : n < 2 ^ 64) :
    decodeLength? (encodeLength n ++ rest) = .ok (n, rest) := by
  have hb : n < 128 ^ (Constants.lengthPrefixMaxBytes - 0) := by
    simp only [Constants.lengthPrefixMaxBytes]; omega
  simp only [decodeLength?, lengthGroupsEncode n 0 rest hb (by decide), bind, Except.bind, h,
    ↓reduceIte, pure, Except.pure]

/-! ## The writer -/

/-- The masked CRC-32C of `data`, little-endian. -/
def checksumB (data : ByteArray) : ByteArray :=
  let m := Crc32c.maskB (Crc32c.crc32cB data)
  ByteArray.mk #[m.toUInt8, (m >>> 8).toUInt8, (m >>> 16).toUInt8, (m >>> 24).toUInt8]

/-- The block compressor the writer calls: the `codec/snappy` binding. -/
abbrev Compressor := ByteArray → Except Snappy.Error ByteArray

/-- One data chunk for at most 65536 bytes: compressed when the block
is shorter than the raw bytes, uncompressed otherwise. -/
def dataChunkB (block : ByteArray) (compress : Compressor := Snappy.compress) : ByteArray :=
  let crc := checksumB block
  match compress block with
  | .ok c =>
    if c.size < block.size then
      SnappyFrame.headerB .compressed (c.size + Constants.snappyCrcLen) ++ crc ++ c
    else SnappyFrame.headerB .uncompressed (block.size + Constants.snappyCrcLen) ++ crc ++ block
  -- A block of at most 65536 bytes is far below the 2^32 limit, so this
  -- arm does not occur; the raw chunk is valid either way.
  | .error _ => SnappyFrame.headerB .uncompressed (block.size + Constants.snappyCrcLen) ++ crc ++ block

/-- The stream identifier chunk, which opens every framed stream. -/
def streamIdB : ByteArray :=
  SnappyFrame.headerB .streamId Constants.snappyStreamBody.length ++
    ByteArray.mk (Constants.snappyStreamBody.map (·.toUInt8)).toArray

/-- A framed stream of `payload`: the identifier, then one data chunk
per 65536 bytes. The empty payload is the identifier alone; a reader of
`n = 0` reads no frame (see `ReqResp/Core.lean`). The compressor is an
argument so the suite can drive the error arm of `dataChunkB`. -/
def encodeFramesB (payload : ByteArray) (compress : Compressor := Snappy.compress) :
    ByteArray := Id.run do
  let mut out := streamIdB
  let blocks := (payload.size + Constants.snappyMaxDataLen - 1) / Constants.snappyMaxDataLen
  for i in [0:blocks] do
    let start := i * Constants.snappyMaxDataLen
    out := out ++ dataChunkB (payload.extract start (start + Constants.snappyMaxDataLen)) compress
  return out

/-- The length prefix on the `ByteArray` path. -/
def encodeLengthB (n : Nat) : ByteArray := ByteArray.mk ((encodeLength n).map (·.toUInt8)).toArray

/-- One payload on the wire: the prefix, then the framed stream. The
empty payload has the prefix alone, since a reader of `n = 0` stops
after it. -/
def encodePayloadB (payload : ByteArray) (compress : Compressor := Snappy.compress) :
    ByteArray :=
  if payload.size = 0 then encodeLengthB 0
  else encodeLengthB payload.size ++ encodeFramesB payload compress

/-- A request, after the writer checks it against the method. A method
with no request content writes nothing, and takes no payload. -/
def encodeRequestB (m : Method) (payload : Option ByteArray) : Except Error ByteArray :=
  match m.request, payload with
  | none, none => .ok ByteArray.empty
  | some b, some p =>
    if b.admits p.size then .ok (encodePayloadB p) else .error (.payloadOutOfBounds p.size)
  | none, some p => .error (.payloadOutOfBounds p.size)
  | some _, none => .error (.payloadOutOfBounds 0)

/-- One response chunk, after the writer checks it. A success chunk
carries `contextLen` context bytes and fits the bounds. An error chunk
carries no context and an `ErrorMessage` of at most 256 bytes. -/
def encodeChunkB (m : Method) (c : Chunk) : Except Error ByteArray :=
  let code := ByteArray.mk #[c.result.toCode.toUInt8]
  match c.result with
  | .success =>
    if c.context.size ≠ m.contextLen then .error (.payloadOutOfBounds c.context.size)
    else if m.response.admits c.payload.size then
      .ok (code ++ c.context ++ encodePayloadB c.payload)
    else .error (.payloadOutOfBounds c.payload.size)
  | _ =>
    if Bounds.errorMessage.admits c.payload.size ∧ c.context.size = 0 then
      .ok (code ++ encodePayloadB c.payload)
    else .error (.payloadOutOfBounds c.payload.size)

end Libp2p.Protocols.ReqResp
