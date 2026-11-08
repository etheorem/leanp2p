import Tests.Support
import Libp2p.Protocols.ReqResp.Exchange
import Libp2p.Protocols.Mock.Muxer
import Libp2p.Protocols.Mock.HostStream
import Multiformats.Multiaddr

/-!
# The req/resp suite (root PLAN W6.3)

Upstream: the consensus networking spec,
`vendor/consensus-specs/specs/phase0/p2p-interface.md` ("The Req/Resp
domain") and `vendor/consensus-specs/specs/altair/p2p-interface.md`
("Req-Resp interaction"), the snappy formats under `vendor/snappy`,
RFC 3720 appendix B.4 for CRC-32C, and
`Tests/fixtures/reqresp-snappy-go.json`, the payloads that prysm's
encoder shape writes through go's snappy.

The sections follow the layers: the checksum, the chunk codec, the
length prefix, the reader core as transcripts with no clock and no
task, the writer, the concurrency limit, the exchange over a stream
pair with the test clock, and the exchange over the sim transport
through the mock muxer and the host stream mock.
-/

set_option autoImplicit false

namespace Tests.ReqResp

open Tests
open Conc (Async Chan Clock OnceRef TaskSet TestClock)
open Libp2p.Protocols
open Libp2p.Protocols.ReqResp

/-! ## Helpers -/

/-- The bytes of a list of numbers. -/
def bs (l : List Nat) : ByteArray := ByteArray.mk (l.map (·.toUInt8)).toArray

/-- A fixed sequence of `n` bytes, the same on every run. -/
def noise (seed n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut x := seed
  for _ in [0:n] do
    x := (x * 1664525 + 1013904223) % 2 ^ 32
    out := out.push (x / 2 ^ 24).toUInt8
  return out

/-- A method for the transcripts: payloads of 0 to 200000 bytes, the
`ForkDigest` context when `ctx`, and at most `maxChunks` chunks. -/
def method (ctx : Bool := false) (maxChunks : Nat := 4) (request : Option Bounds := some ⟨0, 200000⟩) :
    Method :=
  ⟨Constants.reqRespId "test_method" 1, request, ⟨0, 200000⟩,
    if ctx then Constants.forkDigestLen else 0, maxChunks⟩

/-- Feed `pieces` to a reader, then the end of the stream when `eof`. -/
def feed (st : Core.State) (pieces : List ByteArray) (eof : Bool := true) :
    Except Error (Core.State × List Core.Action) := do
  let mut st := st
  let mut acts : List Core.Action := []
  for p in pieces do
    let (s, a) ← Core.step st (.bytes p)
    st := s
    acts := acts ++ a
  if eof then
    let (s, a) ← Core.step st .eof
    st := s
    acts := acts ++ a
  return (st, acts)

/-- The payloads of the chunk actions. -/
def payloads (acts : List Core.Action) : List ByteArray :=
  acts.filterMap fun | .chunk c => some c.payload | .finished => none

/-- The pieces of `b`, one byte each. -/
def bytewise (b : ByteArray) : List ByteArray := b.toList.map fun x => ByteArray.mk #[x]

/-- The pieces of `b`, `k` bytes each. -/
def piecesOf (k : Nat) (b : ByteArray) : List ByteArray :=
  (List.range ((b.size + k - 1) / k)).map fun i => b.extract (k * i) (k * i + k)

/-- A responder reader of method `m`. -/
def requestReader (m : Method) : Core.State := Core.init m.requestConfig m.request.isSome

/-- A requester reader of method `m`. -/
def responseReader (m : Method) : Core.State := Core.init m.responseConfig

/-- The result of a successful read, or the error. -/
def readRequest (m : Method) (pieces : List ByteArray) : Except Error (List ByteArray) :=
  (feed (requestReader m) pieces).map fun (_, acts) => payloads acts

/-- A success chunk on the wire, or empty when the writer refuses it. -/
def chunkWire (m : Method) (c : Chunk) : ByteArray :=
  (encodeChunkB m c).toOption.getD ByteArray.empty

/-! ## CRC-32C -/

def crcChecks (r : Runner) : IO Unit := do
  r.section "CRC-32C" "RFC 3720 appendix B.4; framing_format.txt section 3"
  -- The four examples of RFC 3720, B.4, as the CRC value.
  let cases : List (String × List Nat × Nat) :=
    [("32 bytes of zeros", List.replicate 32 0, 0x8a9136aa),
     ("32 bytes of ones", List.replicate 32 0xff, 0x62a8ab43),
     ("32 incrementing bytes", List.range 32, 0x46dd794e),
     ("32 decrementing bytes", (List.range 32).reverse, 0x113fdb5c)]
  for (name, l, want) in cases do
    r.check s!"crc32c model: {name}" (Crc32c.crc32c l == want)
    r.check s!"crc32c bytes: {name}" ((Crc32c.crc32cB (bs l)).toNat == want)
  -- The table path agrees with the bit-by-bit model.
  let pins := (List.range 40).all fun i =>
    let b := noise (i + 7) (i * 37)
    (Crc32c.crc32cB b).toNat == Crc32c.crc32c (Bytes.toNatList b)
  r.check "crc32cB equals the model on 40 inputs of 0 to 1443 bytes" pins
  let masks := (List.range 40).all fun i =>
    let x := (noise (i + 3) 4).foldl (fun a y => a * 256 + y.toNat) 0
    (Crc32c.maskB x.toUInt32).toNat == Crc32c.mask x
  r.check "maskB equals the model mask on 40 values" masks
  -- The mask of section 3, by hand: rotate right by 15, then add.
  r.check "mask 0 is the constant" (Crc32c.mask 0 == Constants.snappyMaskDelta)

/-! ## The chunk codec -/

def chunkChecks (r : Runner) : IO Unit := do
  r.section "snappy chunks" "framing_format.txt sections 1 and 4"
  r.check "every byte value names a chunk kind"
    ((List.range 256).all fun c => (SnappyFrame.Kind.ofCode? c).isSome)
  r.check "no kind past the byte range" ((SnappyFrame.Kind.ofCode? 256).isNone)
  let mk (k : SnappyFrame.Kind) (body : List Nat) : Option SnappyFrame.Chunk :=
    if h : body.length ≤ Constants.snappyMaxChunkLen ∧ ∀ b ∈ body, b < 256 then
      some ⟨k, body, h.1, h.2⟩
    else none
  let samples : List SnappyFrame.Chunk := List.filterMap id
    [mk .streamId Constants.snappyStreamBody, mk .compressed [1, 2, 3, 4, 5],
     mk .uncompressed (List.replicate 300 7), mk .padding [], mk .padding (List.replicate 70000 0),
     mk (.skippable 0x80 (by omega)) [9], mk (.unskippable 0x02 (by omega)) [1, 2]]
  r.check "chunk round trips" (Bytes.checkRoundTrips samples)
  let adapter (b : ByteArray) : Except Bytes.DecodeError (SnappyFrame.Chunk × List Nat) :=
    (SnappyFrame.decodeB? b).map fun (c, k) => (c, Bytes.toNatList (b.extract k b.size))
  let inputs : List ByteArray :=
    samples.map (fun c => bs (SnappyFrame.encode c ++ [5, 6])) ++
    [bs [], bs [0xff], bs [0xff, 6, 0], bs [0xff, 6, 0, 0, 0x73], bs [1, 0, 1, 0], bs [0xfe, 2, 0, 0, 9, 9]] ++
    (List.range 30).map fun i => noise (i + 11) (i % 9)
  r.check "decodeB? equals the model on samples, truncations, and noise"
    (Bytes.checkModelPins adapter inputs)
  r.check "three header bytes are truncated"
    (failsWith Bytes.DecodeError.truncated (SnappyFrame.decode? [0xff, 6, 0]))
  r.check "a body shorter than its length is truncated"
    (failsWith Bytes.DecodeError.truncated (SnappyFrame.decode? [1, 5, 0, 0, 1, 2]))
  r.check "a header entry past 255 is malformed"
    (failsWith Bytes.DecodeError.malformed (SnappyFrame.decode? [1, 300, 0, 0]))

/-! ## The length prefix -/

def lengthChecks (r : Runner) : IO Unit := do
  r.section "length prefix" "phase0 p2p-interface.md, SSZ-snappy encoding strategy"
  let values := [0, 1, 127, 128, 300, 16384, Constants.maxPayloadSize, 2 ^ 63, 2 ^ 64 - 1]
  r.check "the prefix round-trips on the model"
    (values.all fun n => succeedsWith (n, [9]) (decodeLength? (encodeLength n ++ [9])))
  r.check "the ByteArray read agrees with the model"
    (values.all fun n => match Core.lengthB? (encodeLengthB n) with
      | some (.ok (v, k)) => v == n && k == (encodeLength n).length
      | _ => false)
  r.check "a 10-byte prefix of 2^64 - 1 is read" ((encodeLength (2 ^ 64 - 1)).length == 10)
  r.check "a non-minimal prefix is read (minimality is a SHOULD)"
    (succeedsWith (5, []) (decodeLength? [0x85, 0x00]))
  r.check "the ByteArray read takes a non-minimal prefix too"
    (match Core.lengthB? (bs [0x85, 0x80, 0x00]) with | some (.ok (5, 3)) => true | _ => false)
  let eleven := List.replicate 10 0x80 ++ [0]
  r.check "an 11-byte prefix is malformed" (failsWith .malformed (decodeLength? eleven))
  r.check "the ByteArray read refuses 11 bytes"
    (match Core.lengthB? (bs eleven) with | some (.error .lengthPrefix) => true | _ => false)
  let over := List.replicate 9 0xff ++ [0x02]
  r.check "a 10-byte prefix of 2^64 or more is malformed" (failsWith .malformed (decodeLength? over))
  r.check "the ByteArray read refuses 2^64"
    (match Core.lengthB? (bs over) with | some (.error .lengthPrefix) => true | _ => false)
  r.check "a prefix that may continue waits for more"
    ((Core.lengthB? (bs [0x80, 0x80])).isNone)

/-! ## The reader core: requests -/

def requestChecks (r : Runner) : IO Unit := do
  r.section "reader core, requests" "phase0 p2p-interface.md, Responding side"
  let m := method
  let sizes := [0, 1, 34, 65535, 65536, 65537, 140000]
  for n in sizes do
    let p := noise n n
    let wire := (encodeRequestB m (some p)).toOption.getD ByteArray.empty
    r.check s!"a request of {n} bytes reads back whole" (succeedsWith [p] (readRequest m [wire]))
    r.check s!"a request of {n} bytes reads back in 4 KiB pieces"
      (succeedsWith [p] (readRequest m (piecesOf 4096 wire)))
    if n ≤ 34 then
      r.check s!"a request of {n} bytes reads back one byte at a time"
        (succeedsWith [p] (readRequest m (bytewise wire)))
  -- Repetitive data: snappy shortens it, so the writer emits compressed
  -- chunks; the go fixtures below carry go's compressed chunks.
  let rep := bs ((List.range 100000).map (· % 7))
  let wire := (encodeRequestB m (some rep)).toOption.getD ByteArray.empty
  r.check "a repetitive request of 100000 bytes reads back" (succeedsWith [rep] (readRequest m [wire]))
  -- The end of the stream must follow the request.
  r.check "a byte after the request is refused"
    (failsWith .trailingBytes (readRequest m [wire, bs [0]]))
  r.check "an end inside the request is an early EOF"
    (failsWith .truncated (readRequest m [wire.extract 0 (wire.size - 1)]))
  r.check "an end inside the prefix is an early EOF" (failsWith .truncated (readRequest m [bs [0x80]]))
  r.check "an empty stream is no request" (failsWith .truncated (readRequest m []))
  -- A method with "No Request Content".
  let noContent := method (request := none)
  r.check "no request content: the end of the stream is the request"
    (succeedsWith [] (readRequest noContent []))
  r.check "no request content: any byte is refused"
    (failsWith .trailingBytes (readRequest noContent [bs [0]]))
  r.check "the writer of a no-content method writes nothing"
    (succeedsWith ByteArray.empty.data ((encodeRequestB noContent none).map (·.data)))

/-! ## The reader core: framing rules -/

/-- A request header for `n` bytes, then the stream identifier. -/
def opening (n : Nat) : ByteArray := encodeLengthB n ++ streamIdB

/-- One raw data chunk with a correct checksum. -/
def rawChunk (data : ByteArray) : ByteArray :=
  SnappyFrame.headerB .uncompressed (data.size + 4) ++ checksumB data ++ data

def framingChecks (r : Runner) : IO Unit := do
  r.section "reader core, framing" "framing_format.txt sections 3 and 4; SSZ-snappy encoding strategy"
  let m := method
  let p := bs [1, 2, 3, 4, 5]
  r.check "a hand-built frame reads" (succeedsWith [p] (readRequest m [opening 5 ++ rawChunk p]))
  r.check "a data chunk before the identifier is refused"
    (failsWith (.frame .missingStreamId) (readRequest m [encodeLengthB 5 ++ rawChunk p]))
  r.check "padding before the identifier is refused"
    (failsWith (.frame .missingStreamId)
      (readRequest m [encodeLengthB 5 ++ SnappyFrame.headerB .padding 0 ++ streamIdB ++ rawChunk p]))
  r.check "an identifier with the wrong body is refused"
    (failsWith (.frame .badStreamId)
      (readRequest m [encodeLengthB 5 ++ SnappyFrame.headerB .streamId 6 ++ bs [0x73, 0x4e, 0x61, 0x50, 0x70, 0x5a]]))
  r.check "a repeated identifier is skipped (section 4.1)"
    (succeedsWith [p] (readRequest m [opening 5 ++ streamIdB ++ rawChunk p]))
  r.check "padding is skipped (section 4.4)"
    (succeedsWith [p] (readRequest m [opening 5 ++ SnappyFrame.headerB .padding 3 ++ bs [0, 0, 0] ++ rawChunk p]))
  r.check "a skippable chunk is skipped (section 4.6)"
    (succeedsWith [p] (readRequest m [opening 5 ++ SnappyFrame.headerB (.skippable 0x80 (by omega)) 2 ++
      bs [1, 1] ++ rawChunk p]))
  r.check "an unskippable chunk is refused (section 4.5)"
    (failsWith (.frame (.unskippable 2))
      (readRequest m [opening 5 ++ SnappyFrame.headerB (.unskippable 2 (by omega)) 1 ++ bs [0]]))
  let badCrc := opening 5 ++ SnappyFrame.headerB .uncompressed 9 ++ bs [0, 0, 0, 0] ++ p
  r.check "a wrong checksum is refused (section 3)" (failsWith (.frame .badChecksum) (readRequest m [badCrc]))
  r.check "a data chunk shorter than its checksum is refused"
    (failsWith (.frame .shortDataChunk) (readRequest m [opening 5 ++ SnappyFrame.headerB .uncompressed 2 ++ bs [0, 0]]))
  r.check "data past the announced length is refused"
    (failsWith .tooManyBytes (readRequest m [opening 3 ++ rawChunk p]))
  let big := noise 3 65537
  r.check "an uncompressed chunk of 65537 bytes is refused (section 4.3)"
    (failsWith (.frame .dataTooLong) (readRequest m [opening 70000 ++ rawChunk big]))
  let block := (Snappy.compress p).toOption.getD ByteArray.empty
  r.check "a compressed chunk reads"
    (succeedsWith [p] (readRequest m [opening 5 ++ SnappyFrame.headerB .compressed (block.size + 4) ++
      checksumB p ++ block]))
  r.check "a broken block is refused"
    (failsWith (.frame .badBlock) (readRequest m [opening 5 ++ SnappyFrame.headerB .compressed 6 ++
      checksumB p ++ bs [5, 0xff]]))
  -- The budget for n = 5 is 37 framed bytes: the identifier takes 10,
  -- and the two chunks 10 and 11.
  r.check "data split over two chunks reads"
    (succeedsWith [p] (readRequest m [opening 5 ++ rawChunk (bs [1, 2]) ++ rawChunk (bs [3, 4, 5])]))
  r.check "a third chunk for the same 5 bytes is over the budget"
    (failsWith .overBudget (readRequest m [opening 5 ++ rawChunk (bs [1, 2]) ++ rawChunk ByteArray.empty ++
      rawChunk (bs [3, 4, 5])]))
  let twenty := noise 5 20
  r.check "an empty data chunk reads where the budget has room"
    (succeedsWith [twenty] (readRequest m [opening 20 ++ rawChunk ByteArray.empty ++ rawChunk twenty]))

/-! ## The reader core: caps -/

def capChecks (r : Runner) : IO Unit := do
  r.section "reader core, caps" "phase0 p2p-interface.md, SSZ-snappy encoding strategy; ARCHITECTURE §5.1"
  let m := method
  r.check "a length above the type's bound is refused"
    (failsWith (.lengthOutOfBounds 200001) (readRequest m [encodeLengthB 200001]))
  let tight : Method := { m with request := some ⟨8, 16⟩ }
  r.check "a length below the type's bound is refused"
    (failsWith (.lengthOutOfBounds 7) (readRequest tight [encodeLengthB 7]))
  let huge : Method := { m with request := some ⟨0, 2 ^ 40⟩ }
  r.check "a length above MAX_PAYLOAD_SIZE is refused whatever the type says"
    (failsWith (.lengthOutOfBounds (Constants.maxPayloadSize + 1))
      (readRequest huge [encodeLengthB (Constants.maxPayloadSize + 1)]))
  r.check "a 10 MiB length is admitted" (Bounds.admits ⟨0, 2 ^ 40⟩ Constants.maxPayloadSize)
  -- The budget for n = 10 is 32 + 10 + 1 = 43 framed bytes. The header
  -- of a 100-byte padding chunk passes it, and the reader refuses at the
  -- header, before the body arrives.
  r.check "max_compressed_len(10) is 43" (Constants.maxCompressedLen 10 == 43)
  r.check "a chunk header past the budget is refused before its body"
    (failsWith .overBudget (feed (requestReader m) [opening 10 ++ SnappyFrame.headerB .padding 100] (eof := false)))
  -- The identifier takes 10, the data chunk 18, so 15 bytes of padding
  -- (a 4-byte header and 11 zeros) spend the 43 exactly.
  r.check "padding that spends the budget exactly is read"
    (succeedsWith [bs (List.replicate 10 1)]
      (readRequest m [opening 10 ++ SnappyFrame.headerB .padding 11 ++ bs (List.replicate 11 0) ++
        rawChunk (bs (List.replicate 10 1))]))
  r.check "one more padding byte is over the budget"
    (failsWith .overBudget
      (readRequest m [opening 10 ++ SnappyFrame.headerB .padding 12 ++ bs (List.replicate 12 0) ++
        rawChunk (bs (List.replicate 10 1))]))
  r.check "an over-long prefix is refused" (failsWith .lengthPrefix (readRequest m [bs (List.replicate 11 0x80)]))

/-! ## The reader core: responses -/

def responseChecks (r : Runner) : IO Unit := do
  r.section "reader core, responses" "phase0 Requesting side; altair Req-Resp interaction"
  let m := method (ctx := true) (maxChunks := 3)
  let digest := bs [0xaa, 0xbb, 0xcc, 0xdd]
  let ok (p : ByteArray) : Chunk := ⟨.success, digest, p⟩
  let ps := [noise 1 10, noise 2 0, noise 3 70000]
  let wire := ps.foldl (fun acc p => acc ++ chunkWire m (ok p)) ByteArray.empty
  let read (pieces : List ByteArray) (eof : Bool := true) :=
    (feed (responseReader m) pieces eof).map fun (_, acts) => acts
  r.check "three chunks read, then the end"
    (match read [wire] with
      | .ok acts => payloads acts == ps && acts.getLast? == some .finished
      | .error _ => false)
  r.check "three chunks read in 1000-byte pieces"
    (match read (piecesOf 1000 wire) with | .ok acts => payloads acts == ps | .error _ => false)
  let small := [noise 1 10, noise 2 0, noise 3 30]
  let smallWire := small.foldl (fun acc p => acc ++ chunkWire m (ok p)) ByteArray.empty
  r.check "three small chunks read one byte at a time"
    (match read (bytewise smallWire) with | .ok acts => payloads acts == small | .error _ => false)
  r.check "the context bytes of each chunk read back"
    (match read [wire] with
      | .ok acts => acts.all fun | .chunk c => c.context == digest | .finished => true
      | .error _ => false)
  r.check "zero chunks is a response" (match read [] with | .ok [.finished] => true | _ => false)
  -- An error chunk ends the response, and carries no context.
  let err := chunkWire m ⟨.resourceUnavailable, ByteArray.empty, "no such block".toUTF8⟩
  r.check "an error chunk ends the response"
    (match read [chunkWire m (ok (noise 4 5)) ++ err ++ chunkWire m (ok (noise 5 5))] (eof := false) with
      | .ok [.chunk a, .chunk b] => a.result == .success && b.result == .resourceUnavailable &&
          b.payload == "no such block".toUTF8 && b.context.size == 0
      | _ => false)
  r.check "the reader stops after maxChunks chunks"
    (match read [wire ++ chunkWire m (ok (noise 6 3))] (eof := false) with
      | .ok acts => payloads acts == ps
      | .error _ => false)
  let tooLongError := bs [Constants.resultServerError] ++ encodeLengthB 257
  r.check "an error message over 256 bytes is refused"
    (failsWith (.lengthOutOfBounds 257) (read [tooLongError]))
  r.check "every byte value is a result"
    ((List.range 256).all fun c => (Result.ofCode? c).isSome)
  r.check "a reserved code reads as an error result"
    (match read [bs [7] ++ encodeLengthB 0] (eof := false) with
      | .ok [.chunk c] => match c.result with | .reserved 7 _ => true | _ => false
      | _ => false)
  r.check "an end inside the context bytes is an early EOF"
    (failsWith .truncated (read [bs [0, 0xaa, 0xbb]]))
  -- The writer's checks.
  r.check "the writer refuses a success chunk with the wrong context width"
    (failsWith (.payloadOutOfBounds 0) (encodeChunkB m ⟨.success, ByteArray.empty, noise 1 3⟩))
  r.check "the writer refuses an error message over 256 bytes"
    (failsWith (.payloadOutOfBounds 257) (encodeChunkB m ⟨.serverError, ByteArray.empty, noise 1 257⟩))
  r.check "the writer refuses a payload over the type's bound"
    (failsWith (.payloadOutOfBounds 200001) (encodeRequestB (method) (some (noise 1 200001))))

/-! ## The go fixtures -/

def fixtureChecks (r : Runner) : IO Unit := do
  r.section "go fixtures" "Tests/fixtures/reqresp-snappy-go.json (go snappy at prysm's pin)"
  let file := "reqresp-snappy-go.json"
  let j ← loadFixture file
  let m := method
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let payload ← unhex name (← jStr file c "payload")
    let wire ← unhex name (← jStr file c "wire")
    r.check s!"go {name}: the request reads back" (succeedsWith [payload] (readRequest m [wire]))
    r.check s!"go {name}: read in 1000-byte pieces"
      (succeedsWith [payload] (readRequest m (piecesOf 1000 wire)))
    let resp := bs [0] ++ wire
    r.check s!"go {name}: as a response chunk"
      (match (feed (responseReader (method (maxChunks := 1))) [resp]).map (payloads ·.2) with
        | .ok ps => ps == [payload]
        | .error _ => false)
    -- Our writer's bytes can differ from go's, since the two snappy
    -- encoders can pick other matches, and they read back the same.
    let ours := (encodeRequestB m (some payload)).toOption.getD ByteArray.empty
    r.check s!"go {name}: our encoding reads back" (succeedsWith [payload] (readRequest m [ours]))
    if payload.size = 0 then
      r.check "go empty: our writer writes the same bytes, the prefix alone" (ours == wire)

/-! ## The exchange over a stream pair -/

/-- Two streams back to back, over `Stream.ofPort` with a loop that
delivers each write to the peer at once. With `split`, each byte is its
own read, so the peer sees the worst segmentation. A close ends the
peer's inbox; a reset fails both sides, also after a close, as a muxer
delivers a reset after a half-close (`LoopPort.endedBy`). -/
def pair (split : Bool := false) : BaseIO (Streams.Stream × Streams.Stream) := do
  let aIn : Chan (Except Streams.Error ByteArray) ← Chan.newUnbounded
  let bIn : Chan (Except Streams.Error ByteArray) ← Chan.newUnbounded
  let aRst : OnceRef (Option Streams.Error) ← OnceRef.new none
  let bRst : OnceRef (Option Streams.Error) ← OnceRef.new none
  let side (mine peer : Chan (Except Streams.Error ByteArray))
      (myRst peerRst : OnceRef (Option Streams.Error)) : BaseIO Streams.Stream := do
    let completions ← Streams.Completions.new
    Streams.Stream.ofPort {
      inbox := mine
      endedBy := myRst.get
      completions
      postWrite := fun tag bytes => do
        let pieces := if split then bytewise bytes else [bytes]
        for p in pieces do discard <| peer.send (.ok p)
        completions.resolve tag (.ok ())
        return .ok ()
      postConsumed := fun _ => return .ok ()
      postClose := do peer.close; return .ok ()
      postReset := do
        myRst.set (some .reset)
        peerRst.set (some .reset)
        discard <| mine.trySend (.error .reset)
        discard <| peer.trySend (.error .reset)
        mine.close
        peer.close
        return .ok () }
  return (← side aIn bIn aRst bRst, ← side bIn aIn bRst aRst)

def exchangeChecks (r : Runner) : Async Unit := do
  r.section "exchange" "phase0 Req/Resp interaction; ARCHITECTURE §5.4"
  let m := method (ctx := true)
  let digest := bs [1, 2, 3, 4]
  let answer : List Chunk := [⟨.success, digest, noise 9 70000⟩, ⟨.success, digest, noise 8 12⟩]
  for split in [false, true] do
    let tc ← TestClock.new
    let (a, b) ← pair split
    let owner ← TaskSet.new
    let served : OnceRef (Option ByteArray) ← OnceRef.new none
    owner.spawn do
      discard <| serve b m tc.clock 1000 fun req => do served.set req; return answer
    let got ← requestAll a m tc.clock 1000 (some (noise 7 300))
    owner.joinAll
    r.check s!"request and serve (split {split}): the chunks arrive in order"
      (match got with | .ok cs => cs.map (·.payload) == answer.map (·.payload) | .error _ => false)
    r.check s!"request and serve (split {split}): the responder saw the request"
      ((← served.get) == some (noise 7 300))
    tc.close
  -- A method with no request content.
  do
    let tc ← TestClock.new
    let noContent := method (request := none) (maxChunks := 1)
    let (a, b) ← pair
    let owner ← TaskSet.new
    owner.spawn do
      discard <| serve b noContent tc.clock 1000 fun req =>
        return [⟨.success, ByteArray.empty, (if req.isNone then "meta" else "bad").toUTF8⟩]
    let got ← requestAll a noContent tc.clock 1000 none
    owner.joinAll
    r.check "no request content: the request is the half-close"
      (match got with | .ok [c] => c.payload == "meta".toUTF8 | _ => false)
    tc.close
  -- A malformed request gets an InvalidRequest answer.
  do
    let tc ← TestClock.new
    let (a, b) ← pair
    let owner ← TaskSet.new
    let res : OnceRef (Option (Except Error Unit)) ← OnceRef.new none
    owner.spawn do
      res.set (some (← serve b m tc.clock 1000 fun _ => return []))
    discard <| a.write (encodeLengthB 300000)
    a.close
    let st ← pump a (responseReader (method (maxChunks := 1))) fun _ => pure ()
    owner.joinAll
    r.check "a malformed request: the responder reports the bounds"
      ((← res.get).any (failsWith (.lengthOutOfBounds 300000)))
    r.check "a malformed request: the read of the answer ends" (match st with | .ok _ => true | _ => false)
    tc.close
  -- A malformed request: the answer is one InvalidRequest chunk.
  do
    let tc ← TestClock.new
    let (a, b) ← pair
    let owner ← TaskSet.new
    owner.spawn do discard <| serve b m tc.clock 1000 fun _ => return []
    discard <| a.write (bs [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80])
    a.close
    let got : OnceRef (List Chunk) ← OnceRef.new []
    discard <| pump a (responseReader (method (maxChunks := 1))) fun c => got.update (· ++ [c])
    owner.joinAll
    r.check "a malformed request: the answer is InvalidRequest"
      (match ← got.get with | [c] => c.result == .invalidRequest | _ => false)
    tc.close
  -- A silent responder: the requester's deadline resets the stream.
  do
    let tc ← TestClock.new
    let (a, _b) ← pair
    let owner ← TaskSet.new
    let res : OnceRef (Option (Except Error (List Chunk))) ← OnceRef.new none
    owner.spawn do res.set (some (← requestAll a m tc.clock 500 (some (noise 1 4))))
    r.check "a silent responder: the deadline arms" (← tc.nextTimer)
    tc.advance 500
    owner.joinAll
    r.check "a silent responder: the request fails at its deadline"
      ((← res.get).any (failsWith .timeout))
    tc.close
  -- A silent requester: the responder's deadline ends the read.
  do
    let tc ← TestClock.new
    let (_a, b) ← pair
    let owner ← TaskSet.new
    let res : OnceRef (Option (Except Error Unit)) ← OnceRef.new none
    owner.spawn do res.set (some (← serve b m tc.clock 500 fun _ => return []))
    r.check "a silent requester: the deadline arms" (← tc.nextTimer)
    tc.advance 500
    owner.joinAll
    r.check "a silent requester: the responder fails at its deadline"
      ((← res.get).any (failsWith .timeout))
    tc.close
  -- A requester that stops at its last chunk resets a stream the peer
  -- left open, since the rest is no longer relevant.
  do
    let tc ← TestClock.new
    let one := method (maxChunks := 1)
    let (a, b) ← pair
    let owner ← TaskSet.new
    owner.spawn do
      -- Read the request to its end, answer one chunk, and stay open.
      discard <| pump b (requestReader one) fun _ => pure ()
      discard <| b.write (chunkWire one ⟨.success, ByteArray.empty, noise 2 8⟩)
    let got ← requestAll a one tc.clock 1000 (some (noise 1 4))
    owner.joinAll
    r.check "a stop before the peer's close: the chunk arrives"
      (match got with | .ok [c] => c.payload == noise 2 8 | _ => false)
    -- The requester has returned, so its reset came before this read.
    r.check "a stop before the peer's close: the peer sees the reset"
      (match ← b.read with | .error .reset => true | _ => false)
    tc.close
  -- The handler value maps the error once, at the seam.
  r.check "the handler registers under the method's id"
    ((handler m Clock.system 1000 fun _ => return []).id == m.id)
  r.check "a timeout maps to the coarse timeout arm"
    (match mapError .timeout with | .timeout _ => true | _ => false)
  r.check "a framing error maps to the coarse protocol arm"
    (match mapError (.frame .badChecksum) with | .protocol _ => true | _ => false)
  r.check "the protocol id has the spec's shape"
    ((Constants.reqRespId "status" 1).toString == "/eth2/beacon_chain/req/status/1/ssz_snappy")

/-! ## The writer's compressed branch -/

/-- The kinds of the data chunks of one written payload, in order. The
walk starts after the length prefix and the stream identifier. -/
def chunkKinds (payloadSize : Nat) (wire : ByteArray) : List SnappyFrame.Kind := Id.run do
  let mut pos := (encodeLengthB payloadSize).size + streamIdB.size
  let mut kinds := []
  -- Every chunk carries at least its 4-byte header, so the loop runs
  -- at most `wire.size` times.
  for _ in [0:wire.size] do
    let some (.ok (k, len)) := SnappyFrame.decodeHeaderB? wire pos | break
    kinds := kinds ++ [k]
    pos := pos + Constants.snappyHeaderLen + len
  return kinds

def writerChecks (r : Runner) : IO Unit := do
  r.section "writer" "framing_format.txt sections 4.2 and 4.3"
  let m := method
  let run := bs (List.replicate 140000 0x61)
  let wire := encodePayloadB run
  -- The identifier, then three chunks of 65536, 65536, and 8928 bytes.
  -- The binding shrinks each run, so each chunk is compressed.
  r.check "the writer picks compressed chunks when the block is shorter"
    (wire.size < 10000 && chunkKinds run.size wire == [.compressed, .compressed, .compressed])
  r.check "compressed chunks from the writer read back" (succeedsWith [run] (readRequest m [wire]))
  r.check "compressed chunks read back in 1000-byte pieces"
    (succeedsWith [run] (readRequest m (piecesOf 1000 wire)))
  -- A run fills the first chunk, and noise the second. The binding
  -- cannot shrink the noise, so the writer keeps those bytes raw.
  let mixed := bs (List.replicate 65536 0x61) ++ noise 4 1000
  let mixedWire := encodePayloadB mixed
  r.check "a run and noise give a compressed and a raw chunk"
    (chunkKinds mixed.size mixedWire == [.compressed, .uncompressed])
  r.check "a payload of a compressed and a raw chunk reads back"
    (succeedsWith [mixed] (readRequest m [mixedWire]))
  -- A compressor error leaves the chunk raw, and the payload still reads.
  let refuse : Compressor := fun _ => .error .inputTooLarge
  let refusedWire := encodePayloadB run refuse
  r.check "a compressor error gives raw chunks"
    (chunkKinds run.size refusedWire == [.uncompressed, .uncompressed, .uncompressed])
  r.check "raw chunks from a refused compression read back"
    (succeedsWith [run] (readRequest m [refusedWire]))

/-! ## The concurrency limit -/

def limiterChecks (r : Runner) : IO Unit := do
  r.section "concurrency limit" "phase0 p2p-interface.md, Requesting side; Configs"
  let a := Constants.reqRespId "a" 1
  let b := Constants.reqRespId "b" 1
  let t0 : Table := []
  let (ok1, t1) := t0.take a
  let (ok2, t2) := t1.take a
  let (ok3, t3) := t2.take a
  r.check "MAX_CONCURRENT_REQUESTS is 2" (Constants.maxConcurrentRequests == 2)
  r.check "two requests with one id take a slot each" (ok1 && ok2)
  r.check "a third request with the same id is refused" (!ok3 && t3.count a == 2)
  r.check "another id has its own slots" ((t3.take b).1)
  r.check "a give frees a slot" ((t3.give a).take a).1
  let l ← Limiter.new
  let x ← l.take a
  let y ← l.take a
  let z ← l.take a
  l.give a
  let w ← l.take a
  r.check "the limiter refuses the third and takes after a give" (x && y && !z && w)

/-! ## Over the sim transport -/

open Libp2p.Protocols.Mock.Muxer (muxer)
open Libp2p.Protocols.Mock.HostStream (Host)

/-- The peer id of a fixed Ed25519 seed of 32 copies of `v`. -/
private def seedPeer (v : UInt8) : Async Libp2p.Identity.PeerId := do
  let seed : ByteArray := ⟨Array.replicate 32 v⟩
  match (do Libp2p.Identity.PeerId.ofPubKey (← (← Libp2p.Identity.PrivKey.ofData? .ed25519 seed).toPublic)
      : Except Libp2p.Identity.Error Libp2p.Identity.PeerId) with
  | .ok p => return p
  | .error _ => throw (IO.userError "test: the fixed seed derives no peer id")

/-- A connected pair of hosts over a new sim net and the mock muxer.
Each end's handler context names the other end's peer and its own
connection's remote address. -/
def hostPair (split : Bool := false) : Async (Host × Host) := do
  let net ← Streams.Sim.Net.new split
  let addr ← match Multiformats.Multiaddr.parse? "/ip4/127.0.0.1/tcp/4100" with
    | .ok a => pure a
    | .error _ => throw (IO.userError "test address")
  let l ← net.transport.listen addr
  let some c ← net.transport.dial l.addr | throw (IO.userError "dial failed")
  let some s ← l.accept | throw (IO.userError "accept failed")
  l.close
  let .ok cs ← (muxer.«open» .initiator c ByteArray.empty).run | throw (IO.userError "open failed")
  let .ok ss ← (muxer.«open» .responder s ByteArray.empty).run | throw (IO.userError "open failed")
  let client ← seedPeer 1
  let server ← seedPeer 2
  return (← Host.new cs { remotePeer := server, remoteAddr := c.remoteAddr },
    ← Host.new ss { remotePeer := client, remoteAddr := s.remoteAddr })

def simChecks (r : Runner) : Async Unit := do
  r.section "over the sim" "phase0 Req/Resp interaction; ARCHITECTURE §5.4; PRINCIPLES 1.4"
  let m := method (ctx := true)
  let digest := bs [9, 9, 9, 9]
  let answer : List Chunk := [⟨.success, digest, noise 1 70000⟩, ⟨.success, digest, noise 2 5⟩]
  for split in [false, true] do
    let tc ← TestClock.new
    let (client, server) ← hostPair split
    server.setHandler (handler m tc.clock 1000 fun _ => return answer)
    server.serve
    let limiter ← Limiter.new
    let got : OnceRef (List Chunk) ← OnceRef.new []
    let res ← requestPeer client.newStream limiter m tc.clock 1000 (some (noise 3 200))
      fun c => got.update (· ++ [c])
    r.check s!"sim (split {split}): a request through the host gets its chunks"
      (succeedsWith () res && (← got.get).map (·.payload) == answer.map (·.payload))
    r.check s!"sim (split {split}): the handler saw no failure" ((← server.failures.get).isEmpty)
    r.check s!"sim (split {split}): the limiter slot came back" ((← limiter.take m.id) && (← limiter.take m.id))
    client.close
    server.close
    client.join
    server.join
    tc.close
  -- An id the peer does not serve: the stream is reset.
  do
    let tc ← TestClock.new
    let (client, server) ← hostPair
    server.serve
    let res ← requestPeer client.newStream (← Limiter.new) m tc.clock 1000 (some (noise 3 4))
      fun _ => pure ()
    r.check "sim: an id with no handler fails the request with a reset"
      (failsWith (.stream .reset) res)
    client.close
    server.close
    client.join
    server.join
    tc.close
  -- A silent peer over the sim: the deadline resets the stream, and the
  -- connection stays for the next exchange.
  do
    let tc ← TestClock.new
    let (client, server) ← hostPair
    -- The handler takes one read and ends with no answer and no close.
    server.setHandler ⟨m.id, fun _ s => ExceptT.mk do
      discard <| s.read
      return .ok ()⟩
    server.serve
    let owner ← TaskSet.new
    let res : OnceRef (Option (Except Error Unit)) ← OnceRef.new none
    owner.spawn do
      res.set (some (← requestPeer client.newStream (← Limiter.new) m tc.clock 300 (some (noise 3 4))
        fun _ => pure ()))
    r.check "sim: a silent peer, the deadline arms" (← tc.nextTimer)
    tc.advance 300
    owner.joinAll
    r.check "sim: a silent peer fails the request at its deadline" ((← res.get).any (failsWith .timeout))
    tc.close
    client.close
    server.close
    client.join
    server.join
  -- The connection closes under a parked read: the request ends.
  do
    let tc ← TestClock.new
    let (client, server) ← hostPair
    let parked : Chan Unit ← Chan.new 1
    server.setHandler ⟨m.id, fun _ _ => ExceptT.mk do
      discard <| parked.send ()
      return .ok ()⟩
    server.serve
    let owner ← TaskSet.new
    let res : OnceRef (Option (Except Error Unit)) ← OnceRef.new none
    owner.spawn do
      res.set (some (← requestPeer client.newStream (← Limiter.new) m tc.clock 60000 (some (noise 3 4))
        fun _ => pure ()))
    -- The handler ran, so the request is past its write and parks on the read.
    discard <| parked.recv
    client.close
    owner.joinAll
    r.check "sim: a connection closed under a parked read ends the request"
      ((← res.get).any fun e => match e with | .error _ => true | .ok _ => false)
    server.close
    client.join
    server.join
    tc.close

def run (r : Runner) : IO Unit := do
  crcChecks r
  chunkChecks r
  lengthChecks r
  requestChecks r
  framingChecks r
  capChecks r
  responseChecks r
  fixtureChecks r
  writerChecks r
  limiterChecks r
  (exchangeChecks r).run
  (simChecks r).run

end Tests.ReqResp
