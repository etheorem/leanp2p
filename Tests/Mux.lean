import Tests.Support
import Libp2p.Mux
import Libp2p.Mux.Test.Wire

/-!
# Mux suite (unit W5.4)

The constant checks, and the private test-wire codec and parser
(`packages/libp2p/mux/docs/ARCHITECTURE.md`).
-/

set_option autoImplicit false

namespace Tests.Mux.Wire

open Bytes
open Libp2p.Mux.Test.Wire

/-- The largest stream id on the 32-bit field. -/
private def idMax : UInt32 := 0xFFFFFFFF

private theorem id1_ok : (1 : UInt32) ≠ 0 := by decide
private theorem id2_ok : (2 : UInt32) ≠ 0 := by decide
private theorem idMax_ok : idMax ≠ 0 := by decide

private def twoBytes : List Nat := [9, 8]
private def fourBytes : List Nat := [1, 2, 3, 4]
private def capPayload : List Nat := List.replicate testPayloadCap 1

private theorem twoBytes_lt : ∀ x ∈ twoBytes, x < 256 := by decide
private theorem fourBytes_lt : ∀ x ∈ fourBytes, x < 256 := by decide
private theorem oneByte_lt : ∀ x ∈ [7], x < 256 := by decide

private theorem twoBytes_ok : lengthOk Kind.data twoBytes.length = true := by decide
private theorem fourBytes_ok : lengthOk Kind.data fourBytes.length = true := by decide
private theorem oneByte_ok : lengthOk Kind.data [7].length = true := by decide

private theorem capPayload_lt : ∀ x ∈ capPayload, x < 256 := by
  intro x hx
  simp [capPayload, List.mem_replicate] at hx
  omega

private theorem capPayload_ok : lengthOk Kind.data capPayload.length = true := by
  simpa [capPayload, List.length_replicate] using
    (by decide : lengthOk Kind.data testPayloadCap = true)

private def sampleOpen : Frame :=
  Frame.ofControl Kind.open 1 (by decide) id1_ok

private def sampleData : Frame :=
  Frame.ofData 2 twoBytes id2_ok twoBytes_lt twoBytes_ok

private def sampleFin : Frame :=
  Frame.ofControl Kind.fin idMax (by decide) idMax_ok

private def sampleReset : Frame :=
  Frame.ofControl Kind.reset 1 (by decide) id1_ok

private def sampleMaxData : Frame :=
  Frame.ofData idMax [7] idMax_ok oneByte_lt oneByte_ok

private def sampleCap : Frame :=
  Frame.ofData 1 capPayload id1_ok capPayload_lt capPayload_ok

private def sampleFour : Frame :=
  Frame.ofData 1 fourBytes id1_ok fourBytes_lt fourBytes_ok

private def frames : List Frame :=
  [sampleOpen, sampleData, sampleFin, sampleReset, sampleMaxData, sampleCap, sampleFour]

private def overCapLength : UInt32 :=
  UInt32.ofNatLT (testPayloadCap + 1) (by decide)

private def overCapHeader : Header where
  kind := Kind.data
  streamId := 1
  length := overCapLength

private def zeroHeader : Header where
  kind := Kind.open
  streamId := 0
  length := 0

private def headers : List Header := [
  zeroHeader,
  { kind := Kind.open, streamId := 1, length := 0 },
  { kind := Kind.data, streamId := 2, length := 0 },
  overCapHeader,
  { kind := Kind.fin, streamId := idMax, length := 0 },
  { kind := Kind.reset, streamId := 0x01020304, length := 0x01020304 },
]

/-- The production header decoder in the harness shape. -/
private def headerProduction (b : ByteArray) : Except DecodeError (Header × List Nat) :=
  (Header.decodeB? b).map fun (h, rest) => (h, toNatList rest)

/-- The production frame decoder in the harness shape. -/
private def frameProduction (b : ByteArray) : Except DecodeError (Frame × List Nat) :=
  (Frame.decodeB? b).map fun (f, rest) => (f, toNatList rest)

/-- A partial retain stays inside its documented bound.
A ready parser is empty, or it holds at least one header. -/
private def withinBound (p : Parser) : Bool :=
  match p.gap with
  | .empty =>
    if p.hasComplete then headerSize ≤ p.retainedBytes else p.retainedBytes == 0
  | .partialHeader => 0 < p.retainedBytes && p.retainedBytes < headerSize
  | .partialBody =>
    headerSize ≤ p.retainedBytes && p.retainedBytes < headerSize + testPayloadCap

/-- Frames, the gap, the retain, and whether a complete frame remains. -/
private def view (fs : List Frame) (p : Parser) :
    List Frame × Gap × Nat × Bool × Bool :=
  (fs, p.gap, p.retainedBytes, p.hasComplete, withinBound p)

/-- Two feeds, and the view after each one. -/
private def continues (first rest : List Nat)
    (v1 v2 : List Frame × Gap × Nat × Bool × Bool) : Bool :=
  match Parser.feed Parser.empty first with
  | .error _ => false
  | .ok (fs1, p1) =>
    view fs1 p1 == v1 &&
      match Parser.feed p1 rest with
      | .error _ => false
      | .ok (fs2, p2) => view fs2 p2 == v2

/-- Every byte of one frame, split after `i` bytes, reassembles. -/
private def splitAt (frame : Frame) (i : Nat) : Bool :=
  let wire := Frame.encode frame
  match Parser.feed Parser.empty (wire.take i) with
  | .error _ => false
  | .ok (fs1, p1) =>
    match Parser.feed p1 (wire.drop i) with
    | .error _ => false
    | .ok (fs2, p2) =>
      fs1 ++ fs2 == [frame] && p2.gap == .empty && p2.retainedBytes == 0
        && !p2.hasComplete && withinBound p1 && withinBound p2

/-- The same split on `ByteArray` chunks. -/
private def splitBAt (frame : Frame) (i : Nat) : Bool :=
  let wire := Frame.encodeB frame
  match Parser.feedB Parser.empty (wire.extract 0 i) with
  | .error _ => false
  | .ok (fs1, p1) =>
    match Parser.feedB p1 (wire.extract i wire.size) with
    | .error _ => false
    | .ok (fs2, p2) =>
      fs1 ++ fs2 == [frame] && p2.gap == .empty && p2.retainedBytes == 0
        && !p2.hasComplete && withinBound p1 && withinBound p2

/-- The model feed and `feedB` agree on frames and observations. -/
private def aligned (chunk : List Nat) : Bool :=
  match Parser.feed Parser.empty chunk, Parser.feedB Parser.empty (ofNatList chunk) with
  | .ok (fs, p), .ok (fsB, pB) =>
    fs == fsB && p.gap == pB.gap && p.retainedBytes == pB.retainedBytes
      && p.hasComplete == pB.hasComplete && withinBound p && withinBound pB
  | .error e, .error eB => e == eB
  | _, _ => false

/-- The private test wire. -/
def run (r : Runner) : IO Unit := do
  r.section "mux test wire" "packages/libp2p/mux/Libp2p/Mux/Test/Wire.lean"
  r.check "bytes32 1 is big-endian" (bytes32 1 == [0, 0, 0, 1])
  r.check "bytes32 2 is big-endian" (bytes32 2 == [0, 0, 0, 2])
  r.check "bytes32 0x01020304 is big-endian" (bytes32 0x01020304 == [1, 2, 3, 4])
  r.check "bytes32 of the largest stream id is big-endian" (bytes32 idMax == [255, 255, 255, 255])
  r.check "open id 1 encodes kind, id, and a zero length"
    (Frame.encode sampleOpen == Kind.open.toCode :: (bytes32 1 ++ bytes32 0))
  r.check "data id 2 encodes a two-byte payload"
    (Frame.encode sampleData == Kind.data.toCode :: (bytes32 2 ++ bytes32 2 ++ twoBytes))
  r.check "fin at the largest stream id encodes a zero length"
    (Frame.encode sampleFin == Kind.fin.toCode :: (bytes32 idMax ++ bytes32 0))
  r.check "reset id 1 encodes a zero length"
    (Frame.encode sampleReset == Kind.reset.toCode :: (bytes32 1 ++ bytes32 0))
  r.check "data at the largest stream id encodes one payload byte"
    (Frame.encode sampleMaxData == Kind.data.toCode :: (bytes32 idMax ++ bytes32 1 ++ [7]))
  r.check "header round trip keeps a suffix"
    (headers.all fun h => succeedsWith (h, [7]) (Header.decode? (Header.encode h ++ [7])))
  r.check "frame round trip keeps a suffix"
    (frames.all fun f => succeedsWith (f, [4, 5]) (Frame.decode? (Frame.encode f ++ [4, 5])))
  r.check "header round-trip harness" (checkRoundTrips headers)
  r.check "frame round-trip harness" (checkRoundTrips frames)
  r.check "header ByteArray matches the model"
    (headers.all fun h => Header.encodeB h == ofNatList (Header.encode h))
  r.check "frame ByteArray matches the model"
    (frames.all fun f => Frame.encodeB f == ofNatList (Frame.encode f))
  r.check "header ByteArray decode keeps a suffix"
    (headers.all fun h =>
      match Header.decodeB? ((Header.encodeB h).push 9) with
      | .ok (got, rest) => got == h && toNatList rest == [9]
      | .error _ => false)
  r.check "frame ByteArray decode keeps a suffix"
    (frames.all fun f =>
      match Frame.decodeB? ((Frame.encodeB f).push 4) with
      | .ok (got, rest) => got == f && toNatList rest == [4]
      | .error _ => false)
  let headerPins :=
    (headers.map Header.encodeB)
      ++ (headers.map fun h => (Header.encodeB h).push 9)
      ++ ((List.range headerSize).map fun i => ofNatList ((Frame.encode sampleOpen).take i))
      ++ [ofNatList (0 :: bytes32 1 ++ bytes32 0), ofNatList (5 :: bytes32 1 ++ bytes32 0)]
  r.check "header model pin" (checkModelPins headerProduction headerPins)
  let framePins :=
    (frames.map Frame.encodeB)
      ++ (frames.map fun f => (Frame.encodeB f).push 4)
      ++ ((List.range headerSize).map fun i => ofNatList ((Frame.encode sampleOpen).take i))
      ++ [ofNatList (Header.encode zeroHeader),
          ofNatList (Header.encode overCapHeader),
          ofNatList (Header.encode overCapHeader ++ [1]),
          ofNatList (5 :: bytes32 1 ++ bytes32 0),
          ofNatList (Header.encode { kind := Kind.data, streamId := 1, length := 4 } ++ [1, 2, 3])]
  r.check "frame model pin" (checkModelPins frameProduction framePins)
  r.check "kind 0 is malformed" (failsWith .malformed (Header.decode? (0 :: bytes32 1 ++ bytes32 0)))
  r.check "kind 5 is malformed" (failsWith .malformed (Header.decode? (5 :: bytes32 1 ++ bytes32 0)))
  r.check "kind 255 is malformed" (failsWith .malformed (Header.decode? (255 :: bytes32 1 ++ bytes32 0)))
  r.check "a non-byte kind is malformed" (failsWith .malformed (Header.decode? [300]))
  r.check "a non-byte length is malformed"
    (failsWith .malformed (Header.decode? (Kind.open.toCode :: (bytes32 1 ++ [0, 0, 0, 300]))))
  r.check "a zero stream id is a header"
    (succeedsWith (zeroHeader, []) (Header.decode? (Header.encode zeroHeader)))
  r.check "a zero stream id is not a frame"
    (failsWith .malformed (Frame.decode? (Header.encode zeroHeader))
      && failsWith .malformed (Parser.feed Parser.empty (Header.encode zeroHeader)))
  r.check "an open with a nonzero length is malformed"
    (failsWith .malformed (Frame.decode? (Header.encode { kind := Kind.open, streamId := 1, length := 1 } ++ [9])))
  r.check "a fin with a nonzero length is malformed"
    (failsWith .malformed (Frame.decode? (Header.encode { kind := Kind.fin, streamId := 1, length := 1 } ++ [9])))
  r.check "a reset with a nonzero length is malformed"
    (failsWith .malformed (Frame.decode? (Header.encode { kind := Kind.reset, streamId := 1, length := 1 } ++ [9])))
  r.check "a data frame of length zero is malformed"
    (failsWith .malformed (Frame.decode? (Header.encode { kind := Kind.data, streamId := 1, length := 0 })))
  r.check "a data frame at the cap round-trips"
    (succeedsWith (sampleCap, []) (Frame.decode? (Frame.encode sampleCap)))
  -- The header alone is `malformed`. The cap check returns before a body read.
  r.check "a data length one above the cap is malformed with no body"
    (failsWith .malformed (Frame.decode? (Header.encode overCapHeader))
      && failsWith .malformed (Frame.decodeB? (Header.encodeB overCapHeader))
      && failsWith .malformed (Parser.feed Parser.empty (Header.encode overCapHeader))
      && failsWith .malformed (Parser.feedB Parser.empty (Header.encodeB overCapHeader)))
  r.check "a data length one above the cap keeps no body prefix"
    (failsWith .malformed (Parser.feed Parser.empty (Header.encode overCapHeader ++ [1]))
      && failsWith .malformed (Parser.feedB Parser.empty (ofNatList (Header.encode overCapHeader ++ [1])))
      && failsWith .malformed (Frame.decode? (Header.encode overCapHeader ++ [1])))
  let openBytes := Frame.encode sampleOpen
  for i in List.range headerSize do
    let head := openBytes.take i
    r.check s!"model header truncated at {i}" (failsWith .truncated (Header.decode? head))
    r.check s!"model frame truncated at {i}" (failsWith .truncated (Frame.decode? head))
    r.check s!"bytes header truncated at {i}" (failsWith .truncated (Header.decodeB? (ofNatList head)))
    r.check s!"bytes frame truncated at {i}" (failsWith .truncated (Frame.decodeB? (ofNatList head)))
  let bodyHeader : Header := { kind := Kind.data, streamId := 1, length := 4 }
  let shortBody := Header.encode bodyHeader ++ [1, 2, 3]
  r.check "a short data body is truncated"
    (failsWith .truncated (Frame.decode? shortBody)
      && failsWith .truncated (Frame.decodeB? (ofNatList shortBody)))
  r.check "a short data body waits as a partial body"
    (continues shortBody [4]
      ([], .partialBody, headerSize + 3, false, true)
      ([sampleFour], .empty, 0, false, true))
  let dataBytes := Frame.encode sampleData
  for i in List.range (dataBytes.length + 1) do
    r.check s!"model data frame split at {i}" (splitAt sampleData i)
    r.check s!"bytes data frame split at {i}" (splitBAt sampleData i)
  let many := Frame.encode sampleOpen ++ Frame.encode sampleData ++ Frame.encode sampleFin
  r.check "three frames arrive in one chunk"
    (continues many []
      ([sampleOpen, sampleData, sampleFin], .empty, 0, false, true)
      ([], .empty, 0, false, true))
  let finBytes := Frame.encode sampleFin
  let partialNext := Frame.encode sampleOpen ++ finBytes.take 3
  r.check "a complete frame can leave a partial header"
    (continues partialNext (finBytes.drop 3)
      ([sampleOpen], .partialHeader, 3, false, true)
      ([sampleFin], .empty, 0, false, true))
  r.check "a partial header continues in the next chunk"
    (continues (openBytes.take 4) (openBytes.drop 4)
      ([], .partialHeader, 4, false, true)
      ([sampleOpen], .empty, 0, false, true))
  r.check "an empty parser has an empty gap"
    (Parser.empty.gap == .empty && Parser.empty.retainedBytes == 0
      && !Parser.empty.hasComplete && withinBound Parser.empty)
  r.check "an empty feed leaves the empty gap"
    (continues [] []
      ([], .empty, 0, false, true)
      ([], .empty, 0, false, true))
  r.check "empty, partial header, and partial body stay distinct"
    (Gap.empty != .partialHeader && Gap.empty != .partialBody
      && Gap.partialHeader != .partialBody)
  let burst := 2 * parserFrameBudget + 1
  let burstBytes := (List.replicate burst (Frame.encode sampleOpen)).flatten
  r.check "a burst keeps frames past the budget"
    (parserFrameBudget == 8 &&
      match Parser.feed Parser.empty burstBytes with
      | .ok (first, p1) =>
        first.length == 8 && first.all (· == sampleOpen)
          && p1.hasComplete && p1.gap == .empty
          && p1.retainedBytes == (parserFrameBudget + 1) * headerSize
          && withinBound p1
          && match Parser.drain p1 with
            | .ok (second, p2) =>
              second.length == 8 && second.all (· == sampleOpen)
                && p2.hasComplete && p2.retainedBytes == headerSize
                && withinBound p2
                && match Parser.drain p2 with
                  | .ok (third, p3) =>
                    third.length == 1 && third.all (· == sampleOpen)
                      && !p3.hasComplete && p3.retainedBytes == 0 && p3.gap == .empty
                      && withinBound p3
                  | .error _ => false
            | .error _ => false
      | .error _ => false)
  r.check "the burst agrees on the model and the byte path"
    (aligned burstBytes)
  let mut capParser := Parser.empty
  let mut capFrames : List Frame := []
  let mut capOk := true
  for b in Frame.encode sampleCap do
    if capOk then
      match Parser.feed capParser [b] with
      | .ok (fs, p1) =>
        if withinBound p1 && p1.retainedBytes < headerSize + testPayloadCap then
          capFrames := capFrames ++ fs
          capParser := p1
        else
          capOk := false
      | .error _ => capOk := false
  r.check "a cap frame arrives one byte at a time"
    (capOk && capFrames == [sampleCap] && capParser.gap == .empty
      && capParser.retainedBytes == 0 && !capParser.hasComplete)
  let mut capParserB := Parser.empty
  let mut capFramesB : List Frame := []
  let mut capOkB := true
  let capWire := Frame.encodeB sampleCap
  for i in List.range capWire.size do
    if capOkB then
      match Parser.feedB capParserB (capWire.extract i (i + 1)) with
      | .ok (fs, p1) =>
        if withinBound p1 && p1.retainedBytes < headerSize + testPayloadCap then
          capFramesB := capFramesB ++ fs
          capParserB := p1
        else
          capOkB := false
      | .error _ => capOkB := false
  r.check "a cap frame arrives one byte at a time on bytes"
    (capOkB && capFramesB == [sampleCap] && capParserB.gap == capParser.gap
      && capParserB.retainedBytes == capParser.retainedBytes
      && capParserB.hasComplete == capParser.hasComplete)
  let wide := capWire ++ Frame.encodeB sampleOpen
  r.check "a chunk above the payload cap parses"
    (testPayloadCap < wide.size &&
      match Parser.feedB Parser.empty wide with
      | .ok (fs, p) =>
        fs == [sampleCap, sampleOpen] && p.gap == .empty
          && p.retainedBytes == 0 && !p.hasComplete
      | .error _ => false)
  let bodyAt := headerSize + 1
  r.check "a partial body survives an empty feed"
    (match Parser.feed Parser.empty (Frame.encode sampleFour |>.take bodyAt) with
      | .ok ([], pHeader) =>
        pHeader.gap == .partialBody && pHeader.retainedBytes == headerSize + 1
          && !pHeader.hasComplete && withinBound pHeader
          && match Parser.feed pHeader [] with
            | .ok ([], pStill) =>
              pStill.gap == .partialBody && pStill.retainedBytes == headerSize + 1
                && withinBound pStill
                && match Parser.feed pStill (Frame.encode sampleFour |>.drop bodyAt) with
                  | .ok ([got], pDone) =>
                    got == sampleFour && pDone.gap == .empty && pDone.retainedBytes == 0
                      && !pDone.hasComplete
                  | _ => false
            | _ => false
      | _ => false)
  r.check "an empty feed leaves a partial header in place"
    (match Parser.feed Parser.empty (openBytes.take 4) with
      | .ok ([], p1) =>
        p1.gap == .partialHeader && p1.retainedBytes == 4 && withinBound p1
          && match Parser.feed p1 [] with
            | .ok ([], p2) =>
              p2.gap == .partialHeader && p2.retainedBytes == 4 && !p2.hasComplete
                && match Parser.feed p2 (openBytes.drop 4) with
                  | .ok ([got], p3) =>
                    got == sampleOpen && !p3.hasComplete && p3.retainedBytes == 0
                  | _ => false
            | _ => false
      | _ => false)
  let followed := Frame.encode sampleFour ++ Frame.encode sampleOpen ++ finBytes.take 3
  r.check "a finished body can leave complete and partial frames"
    (continues followed (finBytes.drop 3)
      ([sampleFour, sampleOpen], .partialHeader, 3, false, true)
      ([sampleFin], .empty, 0, false, true))
  let overBytes := Header.encode overCapHeader
  r.check "a cap-plus-one header fails before a body is retained"
    (match Parser.feed Parser.empty (overBytes.take 4) with
      | .ok ([], p1) =>
        p1.gap == .partialHeader && p1.retainedBytes == 4 && withinBound p1
          && failsWith .malformed (Parser.feed p1 (overBytes.drop 4 ++ List.replicate 32 1))
          && p1.gap == .partialHeader && p1.retainedBytes == 4 && !p1.hasComplete
      | _ => false)
  r.check "the model and byte paths agree on the sample chunk"
    (aligned many && aligned shortBody && aligned overBytes
      && aligned (Frame.encode sampleCap) && aligned followed)

end Tests.Mux.Wire

namespace Tests

open Libp2p.Mux

def Mux.run (r : Runner) : IO Unit := do
  r.section "mux constants" "packages/libp2p/mux/docs/ARCHITECTURE.md"
  r.check "yamuxId.toString is /yamux/1.0.0"
    (yamuxId.toString == "/yamux/1.0.0")
  r.check "mplexId.toString is /mplex/6.7.0"
    (mplexId.toString == "/mplex/6.7.0")
  r.check "testId.toString is /leanp2p/test-mux/1.0.0"
    (testId.toString == "/leanp2p/test-mux/1.0.0")
  r.check "mplexMessageCap is 1 MiB"
    (mplexMessageCap == 1024 * 1024)
  r.check "the three protocol ids are pairwise distinct"
    (yamuxId.toString != mplexId.toString
      && yamuxId.toString != testId.toString
      && mplexId.toString != testId.toString)
  Mux.Wire.run r

end Tests
