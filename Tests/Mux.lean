import Tests.Support
import Libp2p.Mux
import Libp2p.Mux.Mock.Core
import Libp2p.Mux.Test.Wire
import Libp2p.Mux.Test.State
import Libp2p.Mux.Test.Session
import Conc
import Streams
import Streams.Mock.Multiaddr

/-!
# Mux suite (unit W5.4)

The constant checks, the temporary core seam, the private
test-wire codec and parser, the pure session transitions, and the
runtime shell (`packages/libp2p/mux/docs/ARCHITECTURE.md`).
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

namespace Tests.Mux.Seam

open Libp2p.Mux
open Libp2p.Mux.Mock.Core

/-- The detail carried by one seam error. -/
private def detail : Error → String
  | .protocol d => d
  | .authentication d => d
  | .timeout d => d
  | .closed d => d

example (s : MuxSession) :
    ProtocolId → ExceptT Error Conc.Async Streams.Stream :=
  s.openStream

example (s : MuxSession) : Conc.Async (Option Streams.Stream) :=
  s.accept

example (s : MuxSession) : IO Unit :=
  s.close

example (s : MuxSession) : Conc.Async (Except Error Unit) :=
  s.join

example (m : Muxer) :
    Role → Streams.Connection → ByteArray → ExceptT Error Conc.Async MuxSession :=
  m.open

/-- A value with `Mux.testId` and the seam fields. It runs no session. -/
example : Muxer := {
  id := testId
  «open» := fun _ _ _ =>
    pure {
      openStream := fun _ => throw (Error.closed "unused")
      accept := pure none
      close := pure ()
      join := pure (.ok ())
    }
}

/-- The temporary seam types. -/
def run (r : Runner) : IO Unit := do
  r.section "mux core seam" "packages/libp2p/mux/Libp2p/Mux/Mock/Core.lean"
  r.check "the two roles are distinct"
    (decide (Role.initiator ≠ Role.responder))
  let p := Error.protocol "wire"
  let a := Error.authentication "wire"
  let t := Error.timeout "wire"
  let c := Error.closed "wire"
  r.check "the four error arms keep their detail and stay distinct"
    (detail p == "wire" && detail a == "wire" && detail t == "wire" && detail c == "wire"
      && decide (p ≠ a) && decide (p ≠ t) && decide (p ≠ c)
      && decide (a ≠ t) && decide (a ≠ c) && decide (t ≠ c))

end Tests.Mux.Seam

namespace Tests.Mux.State

open Libp2p.Mux.Mock.Core
open Libp2p.Mux.Test.Wire
open Libp2p.Mux.Test.State

private def byte (n : UInt8) : ByteArray :=
  ⟨#[n]⟩

private def filled (n : Nat) (v : UInt8) : ByteArray :=
  ⟨Array.replicate n v⟩

private def tally (p : Action → Bool) (as : List Action) : Nat :=
  as.foldl (fun n a => if p a then n + 1 else n) 0

private def isLivePermit : Action → Bool
  | .returnLivePermit => true
  | _ => false

private def isWritePermit : Action → Bool
  | .returnWritePermit _ => true
  | _ => false

private def livePermits (as : List Action) : Nat :=
  tally isLivePermit as

private def writePermits (as : List Action) : Nat :=
  tally isWritePermit as

private def writePermitIds (as : List Action) : List UInt32 :=
  as.filterMap fun a =>
    match a with
    | .returnWritePermit id => some id
    | _ => none

private def acceptPermitIds (as : List Action) : List UInt32 :=
  as.filterMap fun a =>
    match a with
    | .returnAcceptPermit id => some id
    | _ => none

private def okW : Except Streams.Error Unit := .ok ()

private def resetW : Except Streams.Error Unit := .error .reset

private def closedW : Except Streams.Error Unit := .error .closed

private def resolutions (as : List Action) : List (Nat × Except Streams.Error Unit) :=
  as.filterMap fun a =>
    match a with
    | .resolveWrite tag result => some (tag, result)
    | _ => none

private def answerEq (a b : Except Streams.Error Unit) : Bool :=
  match a, b with
  | .ok (), .ok () => true
  | .error x, .error y => x == y
  | _, _ => false

private def answersEq : List (Nat × Except Streams.Error Unit) →
    List (Nat × Except Streams.Error Unit) → Bool
  | [], [] => true
  | (t1, a1) :: xs, (t2, a2) :: ys =>
    t1 == t2 && answerEq a1 a2 && answersEq xs ys
  | _, _ => false

private def resolveCount (tag : Nat) (result : Except Streams.Error Unit)
    (as : List Action) : Nat :=
  tally (fun a =>
    match a with
    | .resolveWrite t r => t == tag && answerEq r result
    | _ => false) as

private def isProtocol (c : Cause) (e : Error) : Bool :=
  Cause.isProtocol c e

private def isRunning (c : Cause) : Bool :=
  match c with
  | .running => true
  | _ => false

private def isOwnerClose (c : Cause) : Bool :=
  match c with
  | .ownerClose => true
  | _ => false

private def isConnectionEnd (c : Cause) : Bool :=
  match c with
  | .connectionEnd => true
  | _ => false

private def faultText (c : Cause) : Option String :=
  match Cause.fault? c with
  | some e => some (toString e)
  | none => none

private def terminalText (as : List Action) : Option String :=
  as.foldl (fun acc a =>
    match a with
    | .terminal c => faultText c
    | _ => acc) none

private def portEnds (as : List Action) : List (UInt32 × PortEnd) :=
  as.filterMap fun a =>
    match a with
    | .setPort id reason => some (id, reason)
    | _ => none

private def findIdx (p : Action → Bool) (as : List Action) : Option Nat :=
  let rec go : Nat → List Action → Option Nat
    | _, [] => none
    | i, a :: rest => if p a then some i else go (i + 1) rest
  go 0 as

private def isSetPort (id : UInt32) (reason : PortEnd) : Action → Bool
  | .setPort i r => i == id && r == reason
  | _ => false

private def isCloseInbox (id : UInt32) : Action → Bool
  | .closeInbox i => i == id
  | _ => false

/-- `setPort` for this id and reason occurs, and it precedes `closeInbox`. -/
private def portBeforeInbox (as : List Action) (id : UInt32) (reason : PortEnd) : Bool :=
  match findIdx (isSetPort id reason) as, findIdx (isCloseInbox id) as with
  | some i, some j => i < j
  | _, _ => false

private def isCloseWrite (id : UInt32) : Action → Bool
  | .closeWritePermits i => i == id
  | _ => false

/-- `setPort` for this id and reason precedes `closeWritePermits`. -/
private def modeBeforePermits (as : List Action) (id : UInt32) (reason : PortEnd) : Bool :=
  match findIdx (isSetPort id reason) as, findIdx (isCloseWrite id) as with
  | some i, some j => i < j
  | _, _ => false

private def closeWriteIds (as : List Action) : List UInt32 :=
  as.filterMap fun a =>
    match a with
    | .closeWritePermits id => some id
    | _ => none

private def enqueueIds (as : List Action) : List UInt32 :=
  as.filterMap fun a =>
    match a with
    | .enqueueAccept id => some id
    | _ => none

private def closedAccept (a : Action) : Bool :=
  match a with
  | .closeAccept => true
  | _ => false

private def openIds (as : List Action) : List UInt32 :=
  as.filterMap fun a =>
    match a with
    | .resolveOpen (.ok id) => some id
    | _ => none

private def openErrors (as : List Action) : List Error :=
  as.filterMap fun a =>
    match a with
    | .resolveOpen (.error e) => some e
    | _ => none

private def chunkBytes (as : List Action) : List ByteArray :=
  as.filterMap fun a =>
    match a with
    | .sendChunk _ _ bytes => some bytes
    | _ => none

private def chunkIds (as : List Action) : List UInt32 :=
  as.filterMap fun a =>
    match a with
    | .sendChunk id _ _ => some id
    | _ => none

private def chunkTags (as : List Action) : List Nat :=
  as.filterMap fun a =>
    match a with
    | .sendChunk _ tag _ => some tag
    | _ => none

private def sentKinds (as : List Action) : List Kind :=
  as.filterMap fun a =>
    match a with
    | .sendFrame frame => some frame.kind
    | .sendChunk _ _ _ => some .data
    | _ => none

private def delivers (as : List Action) : Nat :=
  tally (fun a => match a with | .deliver _ _ => true | _ => false) as

private def isErr (r : Except InvariantError Step) (e : InvariantError) : Bool :=
  match r with
  | .error got => got == e
  | .ok _ => false

/-- Run one happy-path transition. An invariant error names `op` and
the canonical diagnostic, and it stops that section. -/
private def require {α : Type} (op : String) (x : Except InvariantError α) : ExceptT String IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw s!"{op}: {e.message}"

/-- Append `ackSend` when the step left an intent. -/
private def acknowledged (step : Step) : Except InvariantError Step :=
  if step.state.outbound.isNone then
    .ok step
  else
    match State.ackSend step.state with
    | .ok done => .ok ⟨done.state, step.actions ++ done.actions⟩
    | .error e => .error e

private def openAck (s : State) (id : UInt32) (gotLive gotAccept : Bool) :
    Except InvariantError Step :=
  match State.openRemote s id gotLive gotAccept with
  | .error e => .error e
  | .ok step => acknowledged step

private def localReset (s : State) (id : UInt32) : Except InvariantError Step :=
  match State.resetLocal s id with
  | .error e => .error e
  | .ok step => acknowledged step

private def openN : Nat → State → List UInt32 → Except InvariantError (State × List UInt32)
  | 0, s, ids => .ok (s, ids)
  | n + 1, s, ids =>
    match acknowledged (State.openLocal s) with
    | .error e => .error e
    | .ok step => openN n step.state (ids ++ openIds step.actions)

private def pumpN : Nat → State → List Action → Except InvariantError (State × List Action)
  | 0, s, acc => .ok (s, acc)
  | n + 1, s, acc =>
    match acknowledged (State.pump s) with
    | .error e => .error e
    | .ok step => pumpN n step.state (acc ++ step.actions)

private def admitAll (s : State) (id : UInt32) (start : Nat) (bytes : List ByteArray) :
    State × List Action :=
  let rec go (s : State) (acts : List Action) (n : Nat) : List ByteArray → State × List Action
    | [] => (s, acts)
    | b :: rest =>
      let step := State.admitWrite s id n b
      go step.state (acts ++ step.actions) (n + 1) rest
  go s [] start bytes

private theorem id1 : (1 : UInt32) ≠ 0 := by decide

private def oneByte : List Nat := [9]

private theorem oneByte_lt : ∀ x ∈ oneByte, x < 256 := by decide

private theorem oneByte_ok : lengthOk Kind.data oneByte.length = true := by decide

private def dataFrame : Frame :=
  Frame.ofData 1 oneByte id1 oneByte_lt oneByte_ok

private def twoBytes : List Nat := [1, 2]

private theorem twoBytes_lt : ∀ x ∈ twoBytes, x < 256 := by decide

private theorem twoBytes_ok : lengthOk Kind.data twoBytes.length = true := by decide

private def twoFrame : Frame :=
  Frame.ofData 1 twoBytes id1 twoBytes_lt twoBytes_ok

private def manyFrames (n : Nat) : List Nat :=
  (List.range n).flatMap fun _ => Frame.encode dataFrame

private theorem openNotData : Kind.open ≠ Kind.data := by decide

private theorem id2 : (2 : UInt32) ≠ 0 := by decide

private def openFrame : Frame :=
  Frame.ofControl .open 2 openNotData id2

private def openFrames (n : Nat) : List Nat :=
  (List.range n).flatMap fun _ => Frame.encode openFrame

private def applyAll (s : State) (frames : List Frame) :
    Except InvariantError (State × List Action) :=
  frames.foldlM (fun (acc : State × List Action) f =>
    let (s, acts) := acc
    match State.apply s f with
    | .error e => .error e
    | .ok step => .ok (step.state, acts ++ step.actions)) (s, [])

/-- Local and remote id progression. -/
private def runIds (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let responder := State.empty .responder
  r.check "an initiator starts at local 1 and remote 2"
    (initiator.nextLocal == 1 && initiator.nextRemote == 2)
  r.check "a responder starts at local 2 and remote 1"
    (responder.nextLocal == 2 && responder.nextRemote == 1)
  let (initState, initIds) ← require "openN" (openN 3 initiator [])
  let (respState, respIds) ← require "openN" (openN 3 responder [])
  r.check "an initiator issues 1, 3, and 5"
    (decide (initIds = [1, 3, 5]) && initState.nextLocal == 7)
  r.check "a responder issues 2, 4, and 6"
    (decide (respIds = [2, 4, 6]) && respState.nextLocal == 8)
  r.check "issueId refuses zero"
    (issueId 0 true == none && issueId 0 false == none)
  r.check "issueId refuses the wrong parity"
    (issueId 2 true == none && issueId 1 false == none)
  let zero ← require "openAck" (openAck initiator 0 false false)
  r.check "a zero remote id is a protocol failure and does not advance"
    (isProtocol zero.state.cause protocolZero &&
      zero.state.nextRemote == 2 &&
      livePermits zero.actions == 0 &&
      acceptPermitIds zero.actions == [])
  let wrong ← require "openAck" (openAck initiator 1 false false)
  r.check "a wrong-parity remote id is a protocol failure and does not advance"
    (isProtocol wrong.state.cause protocolParity &&
      wrong.state.nextRemote == 2 &&
      livePermits wrong.actions == 0 &&
      acceptPermitIds wrong.actions == [])
  let reserved ← require "openAck" (openAck initiator 0 true true)
  r.check "a reservation on an invalid open is returned"
    (isProtocol reserved.state.cause protocolZero &&
      reserved.state.nextRemote == 2 &&
      livePermits reserved.actions == 1 &&
      decide (acceptPermitIds reserved.actions = [0]))
  let lastOdd := UInt32.size - 1
  let lastEven := UInt32.size - 2
  let oddOnce ← require "acknowledged" (acknowledged (State.openLocal { initiator with nextLocal := lastOdd }))
  let evenOnce ← require "acknowledged" (acknowledged (State.openLocal { responder with nextLocal := lastEven }))
  r.check "the final initiator id is issued once"
    (decide (openIds oddOnce.actions = [UInt32.ofNatLT lastOdd (by decide)]) &&
      oddOnce.state.nextLocal == lastOdd + 2)
  r.check "the final responder id is issued once"
    (decide (openIds evenOnce.actions = [UInt32.ofNatLT lastEven (by decide)]) &&
      evenOnce.state.nextLocal == UInt32.size)
  let oddStop := State.openLocal oddOnce.state
  let evenStop := State.openLocal evenOnce.state
  r.check "initiator exhaustion keeps the Nat and returns the live permit"
    (oddStop.state.nextLocal == oddOnce.state.nextLocal &&
      oddStop.state.nextLocal ≥ UInt32.size &&
      issueId oddStop.state.nextLocal true == none &&
      isRunning oddStop.state.cause &&
      livePermits oddStop.actions == 1 &&
      decide (openErrors oddStop.actions = [protocolExhausted]) &&
      (oddStop.state.live.get? 1).isNone)
  r.check "responder exhaustion keeps the Nat and returns the live permit"
    (evenStop.state.nextLocal == UInt32.size &&
      issueId evenStop.state.nextLocal false == none &&
      isRunning evenStop.state.cause &&
      livePermits evenStop.actions == 1 &&
      decide (openErrors evenStop.actions = [protocolExhausted]))
  r.check "a fresh session has taken no local id"
    (initiator.nextLocal == firstLocal .initiator && initiator.order.isEmpty &&
      (initiator.live.get? 1).isNone)

/-- Remote admission and permit accounting. -/
private def runAdmission (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  match State.classifyRemote initiator 0, State.classifyRemote initiator 1,
      State.classifyRemote initiator 2 with
  | .error zeroErr, .error parityErr, .ok () =>
    r.check "classifyRemote rejects an open before either permit is reserved"
      (decide (zeroErr = protocolZero) && decide (parityErr = protocolParity))
  | _, _, _ =>
    r.check "classifyRemote rejects an open before either permit is reserved" false
  let blocked ← require "openAck" (openAck initiator 2 false false)
  r.check "a remote open with no reservation resets that id and retires it"
    (blocked.state.nextRemote == 4 && (blocked.state.live.get? 2).isNone &&
      blocked.state.retired 2 && livePermits blocked.actions == 0 &&
      acceptPermitIds blocked.actions == [] &&
      portEnds blocked.actions == [] &&
      decide (sentKinds blocked.actions = [.reset]) &&
      isRunning blocked.state.cause &&
      (blocked.state.writeMode? 2).isNone)
  let held ← require "openAck" (openAck initiator 2 true false)
  r.check "a refused remote open returns the acquired live permit once"
    (held.state.nextRemote == 4 && (held.state.live.get? 2).isNone &&
      held.state.retired 2 && livePermits held.actions == 1 &&
      acceptPermitIds held.actions == [] &&
      portEnds held.actions == [] &&
      decide (sentKinds held.actions = [.reset]))
  let acceptOnly ← require "openAck" (openAck initiator 2 false true)
  r.check "a refused remote open returns the acquired accept permit once"
    (acceptOnly.state.nextRemote == 4 && acceptOnly.state.retired 2 &&
      livePermits acceptOnly.actions == 0 &&
      decide (acceptPermitIds acceptOnly.actions = [2]) &&
      portEnds acceptOnly.actions == [] &&
      (acceptOnly.state.writeMode? 2).isNone)
  let nextRemote ← require "openAck" (openAck held.state 4 true true)
  r.check "the next remote id is accepted after a refusal"
    ((nextRemote.state.live.get? 4).isSome && nextRemote.state.nextRemote == 6 &&
      livePermits nextRemote.actions == 0 &&
      acceptPermitIds nextRemote.actions == [] &&
      decide (enqueueIds nextRemote.actions = [4]) &&
      isRunning nextRemote.state.cause)
  let accepted ← require "openAck" (openAck initiator 2 true true)
  let duplicate ← require "openAck" (openAck accepted.state 2 false false)
  r.check "a duplicate open is a protocol failure and does not advance"
    (isProtocol duplicate.state.cause protocolDuplicate &&
      duplicate.state.nextRemote == accepted.state.nextRemote &&
      livePermits duplicate.actions == 1 &&
      acceptPermitIds duplicate.actions == [] &&
      decide (enqueueIds accepted.actions = [2]) &&
      acceptPermitIds accepted.actions == [])
  let future ← require "openAck" (openAck initiator 6 false false)
  r.check "a future open is a protocol failure and does not advance"
    (isProtocol future.state.cause protocolFuture &&
      future.state.nextRemote == 2 &&
      livePermits future.actions == 0 &&
      acceptPermitIds future.actions == [] &&
      portEnds future.actions == [])
  let sealed := State.claim accepted.state .ownerClose
  r.check "session teardown does not return a transferred accept reservation"
    (livePermits sealed.actions == 1 &&
      acceptPermitIds sealed.actions == [] &&
      tally closedAccept sealed.actions == 1 &&
      portBeforeInbox sealed.actions 2 .sessionClosed &&
      modeBeforePermits sealed.actions 2 .sessionClosed)

/-- Queued writes and completion identity. -/
private def runWrites (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let (opened, ids) ← require "openN" (openN 1 initiator [])
  let id := ids.head!
  let four := [byte 1, byte 2, byte 3, byte 4]
  let (queued, admitActs) := admitAll opened id 1 four
  let (pumped, chunks) ← require "pumpN" (pumpN 4 queued [])
  r.check "four admitted writes stay in admission order"
    (admitActs.isEmpty && queued.admittedCount id == 4 &&
      decide (queued.admittedBytes id = four) &&
      decide (chunkBytes chunks = four) &&
      decide (chunkTags chunks = [1, 2, 3, 4]) &&
      answersEq (resolutions chunks) [(1, okW), (2, okW), (3, okW), (4, okW)] &&
      decide (writePermitIds chunks = [id, id, id, id]) &&
      pumped.admittedCount id == 0)
  let fifth := State.admitWrite queued id 5 (byte 5)
  r.check "a fifth write is not stored and its permit is returned once"
    (fifth.state.admittedCount id == 4 &&
      decide (fifth.state.admittedBytes id = four) &&
      resolveCount 5 closedW fifth.actions == 1 &&
      decide (writePermitIds fifth.actions = [id]))
  let halfFifth := State.halfClose fifth.state id
  let resetFifth ← require "localReset" (localReset fifth.state id)
  let shutFifth := State.claim fifth.state .ownerClose
  r.check "half-close, reset, and shutdown close write admission after the port mode"
    (halfFifth.state.admittedCount id == 4 &&
      resolveCount 5 closedW halfFifth.actions == 0 &&
      modeBeforePermits halfFifth.actions id .halfClosed &&
      decide (closeWriteIds halfFifth.actions = [id]) &&
      resolveCount 5 resetW resetFifth.actions == 0 &&
      modeBeforePermits resetFifth.actions id .reset &&
      decide (closeWriteIds resetFifth.actions = [id]) &&
      resolveCount 5 closedW shutFifth.actions == 0 &&
      modeBeforePermits shutFifth.actions id .sessionClosed &&
      decide (closeWriteIds shutFifth.actions = [id]) &&
      resolveCount 1 closedW shutFifth.actions == 1 &&
      resolveCount 4 closedW shutFifth.actions == 1)
  let halfAgain := State.halfClose halfFifth.state id
  r.check "a second half-close releases nothing"
    (halfAgain.actions.isEmpty)
  let (pair, pairIds) ← require "openN" (openN 2 initiator [])
  let left := pairIds[0]!
  let right := pairIds[1]!
  let (leftQueued, _) := admitAll pair left 1 [byte 1, byte 2]
  let (bothQueued, _) := admitAll leftQueued right 3 [byte 3]
  let (_, bothActs) ← require "pumpN" (pumpN 3 bothQueued [])
  r.check "every tag on two streams resolves once with its own permit"
    (resolveCount 1 okW bothActs == 1 &&
      resolveCount 2 okW bothActs == 1 &&
      resolveCount 3 okW bothActs == 1 &&
      decide (chunkTags bothActs = [1, 3, 2]) &&
      decide (writePermitIds bothActs = [left, right, left]))
  let big := filled (testPayloadCap + 3) 1
  let (large, _) := admitAll opened id 7 [big]
  let (afterLarge, largeActs) ← require "pumpN" (pumpN 2 large [])
  let pieces := chunkBytes largeActs
  r.check "one logical write keeps its tag and byte order across chunks"
    (pieces.length == 2 &&
      (pieces[0]?.map (·.size) == some testPayloadCap) &&
      (pieces[1]?.map (·.size) == some 3) &&
      decide (chunkTags largeActs = [7, 7]) &&
      resolveCount 7 okW largeActs == 1 &&
      decide (writePermitIds largeActs = [id]) &&
      afterLarge.admittedCount id == 0)

/-- FIN, reset, and clean-close lifecycle. -/
private def runLifecycle (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let (opened, ids) ← require "openN" (openN 1 initiator [])
  let id := ids.head!
  let (two, _) := admitAll opened id 1 [byte 1, byte 2]
  let half := State.halfClose two id
  let (afterFin, finActs) ← require "pumpN" (pumpN 3 half.state [])
  r.check "half-close publishes the mode and emits no fin before the queue drains"
    (modeBeforePermits half.actions id .halfClosed &&
      decide (closeWriteIds half.actions = [id]) &&
      decide (portEnds half.actions = [(id, .halfClosed)]) &&
      decide (sentKinds finActs = [.data, .data, .fin]) &&
      decide (chunkTags finActs = [1, 2]) &&
      resolveCount 1 okW finActs == 1 &&
      resolveCount 2 okW finActs == 1)
  let again := State.pump afterFin
  r.check "a second pump does not emit another fin"
    (again.actions.isEmpty)
  let late := State.admitWrite half.state id 9 (byte 9)
  r.check "half-close refuses a new write and returns that permit"
    (late.state.admittedCount id == 2 &&
      resolveCount 9 closedW late.actions == 1 &&
      decide (writePermitIds late.actions = [id]))
  let resetHalf ← require "localReset" (localReset half.state id)
  r.check "reset replaces half-close and does not close admission again"
    (resolveCount 1 resetW resetHalf.actions == 1 &&
      resolveCount 2 resetW resetHalf.actions == 1 &&
      decide (writePermitIds resetHalf.actions = [id, id]) &&
      decide (sentKinds resetHalf.actions = [.reset]) &&
      portBeforeInbox resetHalf.actions id .reset &&
      decide (closeWriteIds resetHalf.actions = []) &&
      livePermits resetHalf.actions == 1 &&
      (resetHalf.state.live.get? id).isNone &&
      (resetHalf.state.writeMode? id).isNone)
  let emptyHalf := State.writeEmpty half.state 3 .halfClosed
  r.check "an empty write after half-close resolves closed"
    (answersEq (resolutions emptyHalf.actions) [(3, closedW)] &&
      writePermits emptyHalf.actions == 0)
  let shutHalf := State.claim half.state .ownerClose
  r.check "shutdown after half-close does not close write admission again"
    (decide (portEnds shutHalf.actions = [(id, .sessionClosed)]) &&
      decide (closeWriteIds shutHalf.actions = []))
  let emptyWrite := State.writeEmpty opened 0 .open
  r.check "an empty write resolves its tag from the port and takes no permit"
    (answersEq (resolutions emptyWrite.actions) [(0, okW)] &&
      writePermits emptyWrite.actions == 0 &&
      emptyWrite.state.admittedCount id == 0)
  let emptyReset := State.writeEmpty opened 1 .reset
  r.check "an empty write on a reset port resolves reset"
    (answersEq (resolutions emptyReset.actions) [(1, resetW)] &&
      writePermits emptyReset.actions == 0)
  let (resetBase, _) := admitAll opened id 1 [byte 1, byte 2]
  let reset ← require "localReset" (localReset resetBase id)
  r.check "reset resolves each admitted tag and returns that stream's permits"
    (resolveCount 1 resetW reset.actions == 1 &&
      resolveCount 2 resetW reset.actions == 1 &&
      decide (writePermitIds reset.actions = [id, id]) &&
      livePermits reset.actions == 1 &&
      decide (sentKinds reset.actions = [.reset]) &&
      (chunkBytes reset.actions).isEmpty &&
      portBeforeInbox reset.actions id .reset)
  r.check "reset removes the id without turning absence into a write mode"
    ((reset.state.live.get? id).isNone && reset.state.retired id &&
      (reset.state.writeMode? id).isNone)
  let later ← require "dataRemote" (State.dataRemote reset.state id oneByte)
  r.check "data for a retired id is ignored"
    (later.actions.isEmpty && isRunning later.state.cause)
  let resetAgain ← require "localReset" (localReset reset.state id)
  r.check "a second reset returns no permit"
    (livePermits resetAgain.actions == 0 && writePermits resetAgain.actions == 0 &&
      resetAgain.actions.isEmpty && portEnds resetAgain.actions == [])
  let remote ← require "openAck" (openAck initiator 2 true true)
  let remoteReset ← require "resetRemote" (State.resetRemote remote.state 2)
  let reopened ← require "openAck" (openAck remoteReset.state 2 false false)
  r.check "an open for a retired id is a protocol failure"
    (remoteReset.state.retired 2 &&
      livePermits remoteReset.actions == 1 &&
      acceptPermitIds remoteReset.actions == [] &&
      decide (enqueueIds remote.actions = [2]) &&
      modeBeforePermits remoteReset.actions 2 .reset &&
      portBeforeInbox remoteReset.actions 2 .reset &&
      decide (sentKinds remoteReset.actions = []) &&
      isProtocol reopened.state.cause protocolDuplicate &&
      reopened.state.nextRemote == remoteReset.state.nextRemote &&
      livePermits reopened.actions == 0 &&
      acceptPermitIds reopened.actions == [] &&
      portEnds reopened.actions == [])
  let fin ← require "finRemote" (State.finRemote opened id)
  r.check "a received fin leaves the local write direction open"
    (decide (fin.state.writeMode? id = some .open) &&
      decide (fin.state.readMode? id = some .fin) &&
      (fin.state.live.get? id).isSome &&
      decide (sentKinds fin.actions = []) &&
      portEnds fin.actions == [])
  let stillWrites := State.admitWrite fin.state id 7 (byte 7)
  r.check "a local write is still admitted after a received fin"
    (stillWrites.actions.isEmpty && stillWrites.state.admittedCount id == 1)
  let secondFin ← require "finRemote" (State.finRemote fin.state id)
  let afterData ← require "apply" (State.apply fin.state dataFrame)
  r.check "a duplicate fin and data after fin are ignored"
    (secondFin.actions.isEmpty && afterData.actions.isEmpty &&
      isRunning afterData.state.cause &&
      decide (afterData.state.readMode? id = some .fin))
  let (bothWays, _) ← require "openN" (openN 1 initiator [])
  let openedLocal ← require "openLocal" (acknowledged (State.openLocal initiator))
  let localId := (openIds openedLocal.actions).head!
  let halfOnly := State.halfClose bothWays localId
  let finOnly ← require "acknowledged" (acknowledged (State.pump halfOnly.state))
  let remoteFin ← require "finRemote" (State.finRemote finOnly.state localId)
  r.check "the live permit returns once, when both directions are closed"
    (livePermits halfOnly.actions == 0 &&
      livePermits finOnly.actions == 0 &&
      portEnds finOnly.actions == [] &&
      (finOnly.state.live.get? localId).isSome &&
      livePermits remoteFin.actions == 1 &&
      portEnds remoteFin.actions == [] &&
      (remoteFin.state.live.get? localId).isNone &&
      (remoteFin.state.writeMode? localId).isNone)

/-- Terminal-cause arbitration. -/
private def runTerminal (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let (opened, ids) ← require "openN" (openN 1 initiator [])
  let id := ids.head!
  let readerErr := IO.userError "reader"
  let first := State.claim opened (.readerFault readerErr)
  let second := State.claim first.state .ownerClose
  r.check "the first terminal claim keeps its IO.Error"
    (faultText first.state.cause == some "reader" &&
      terminalText first.actions == some "reader" &&
      faultText second.state.cause == some "reader" &&
      second.actions.isEmpty)
  let owner := State.claim opened .ownerClose
  let readerAfter := State.claim owner.state (.readerFault (IO.userError "later"))
  r.check "a later reader fault does not replace owner close"
    (isOwnerClose owner.state.cause &&
      isOwnerClose readerAfter.state.cause &&
      readerAfter.actions.isEmpty &&
      terminalText readerAfter.actions == none &&
      faultText owner.state.cause == none)
  r.check "reset does not replace sessionClosed"
    (decide (WriteMode.applyReset .sessionClosed = .sessionClosed) &&
      decide (WriteMode.applyReset .open = .reset) &&
      decide (WriteMode.applyReset .halfClosed = .reset) &&
      decide (WriteMode.applyReset .reset = .reset))
  r.check "session close does not replace reset"
    (decide (WriteMode.applySessionClose .reset = .reset) &&
      decide (WriteMode.applySessionClose .open = .sessionClosed) &&
      decide (WriteMode.applySessionClose .sessionClosed = .sessionClosed))
  let sealed := State.claim opened .ownerClose
  let resetSealed ← require "localReset" (localReset sealed.state id)
  r.check "a session-closed stream stays sessionClosed after reset"
    (decide (sealed.state.writeMode? id = some .sessionClosed) &&
      portBeforeInbox sealed.actions id .sessionClosed &&
      decide (resetSealed.state.writeMode? id = some .sessionClosed) &&
      livePermits resetSealed.actions == 0 &&
      writePermits resetSealed.actions == 0 &&
      portEnds resetSealed.actions == [] &&
      (sentKinds resetSealed.actions).isEmpty)
  let closedWrite := State.writeEmpty sealed.state 8 .sessionClosed
  r.check "a write on a session-closed stream resolves closed"
    (answersEq (resolutions closedWrite.actions) [(8, closedW)])
  let (resetBase, _) := admitAll opened id 1 [byte 1]
  let reset ← require "localReset" (localReset resetBase id)
  let closedAfterReset := State.claim reset.state .ownerClose
  let resetWrite := State.writeEmpty closedAfterReset.state 4 .reset
  r.check "a later session close does not overwrite the reset port action"
    (portBeforeInbox reset.actions id .reset &&
      modeBeforePermits reset.actions id .reset &&
      decide (closeWriteIds reset.actions = [id]) &&
      portEnds closedAfterReset.actions == [] &&
      decide (closeWriteIds closedAfterReset.actions = []) &&
      livePermits closedAfterReset.actions == 0 &&
      answersEq (resolutions resetWrite.actions) [(4, resetW)] &&
      (closedAfterReset.state.writeMode? id).isNone)
  let (pair, pairIds) ← require "openN" (openN 2 initiator [])
  let left := pairIds[0]!
  let right := pairIds[1]!
  let (withLeft, _) := admitAll pair left 10 [byte 1]
  let (withBoth, _) := admitAll withLeft right 11 [byte 2, byte 3]
  let closed := State.claim withBoth .ownerClose
  r.check "teardown returns each stream's write permits and no extra permit"
    (resolveCount 10 closedW closed.actions == 1 &&
      resolveCount 11 closedW closed.actions == 1 &&
      resolveCount 12 closedW closed.actions == 1 &&
      decide (writePermitIds closed.actions = [left, right, right]) &&
      livePermits closed.actions == 2 &&
      acceptPermitIds closed.actions == [] &&
      portBeforeInbox closed.actions left .sessionClosed &&
      modeBeforePermits closed.actions left .sessionClosed &&
      portBeforeInbox closed.actions right .sessionClosed &&
      modeBeforePermits closed.actions right .sessionClosed &&
      !portBeforeInbox closed.actions left .reset &&
      !portBeforeInbox closed.actions right .reset)

/-- Parser-to-state integration and scheduling fairness. -/
private def runParser (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let (opened, _) ← require "openN" (openN 1 initiator [])
  match Parser.feed Parser.empty [1] with
  | .ok ([], held) =>
    let ended := State.inboundEnd (State.setParser initiator held)
    r.check "a partial header at connection end is a protocol failure"
      (decide (held.gap = .partialHeader) &&
        isProtocol ended.state.cause protocolPartial)
    let ignored := State.claim ended.state .connectionEnd
    r.check "a later connection-end claim leaves the partial-frame failure"
      (isProtocol ignored.state.cause protocolPartial && ignored.actions.isEmpty)
  | _ =>
    r.check "a partial header at connection end is a protocol failure" false
    r.check "a later connection-end claim leaves the partial-frame failure" false
  let quiet := State.inboundEnd initiator
  r.check "an empty parser at connection end selects connection end"
    (isConnectionEnd quiet.state.cause &&
      decide (initiator.parser.gap = .empty))
  match Parser.feed Parser.empty ((Frame.encode twoFrame).dropLast) with
  | .ok ([], heldBody) =>
    let ended := State.inboundEnd (State.setParser initiator heldBody)
    r.check "a partial body at connection end is a protocol failure"
      (decide (heldBody.gap = .partialBody) &&
        isProtocol ended.state.cause protocolPartial)
  | _ =>
    r.check "a partial body at connection end is a protocol failure" false
  let budget := parserFrameBudget * 2 + 1
  match Parser.feed Parser.empty (manyFrames budget) with
  | .ok (firstPull, kept) =>
    let pending := State.setParser initiator kept
    let noEnd := State.inboundEnd pending
    let once := State.pull (State.setParser opened kept)
    let twice := State.pull once.state
    let (_, applied) ← require "applyAll" (applyAll once.state once.frames)
    r.check "one pull returns a budget of frames and admits none of them"
      (firstPull.length == parserFrameBudget && kept.hasComplete &&
        noEnd.actions.isEmpty &&
        isRunning noEnd.state.cause &&
        once.frames.length == parserFrameBudget &&
        once.actions.isEmpty &&
        once.state.parser.hasComplete &&
        twice.frames.length == 1 &&
        twice.actions.isEmpty &&
        !twice.state.parser.hasComplete &&
        delivers applied == parserFrameBudget)
  | _ =>
    r.check "one pull returns a budget of frames and admits none of them" false
  match Parser.feed Parser.empty (openFrames (parserFrameBudget + 1)) with
  | .ok (_, keptOpen) =>
    let pulled := State.pull (State.setParser initiator keptOpen)
    let ignored ←
      match pulled.frames.head? with
      | some frame => require "apply" (State.apply pulled.state frame)
      | none => pure ⟨pulled.state, []⟩
    let committed ← require "openAck" (openAck pulled.state 2 true true)
    r.check "a pulled open waits for an explicit reservation"
      (keptOpen.hasComplete &&
        pulled.frames.length == 1 &&
        pulled.actions.isEmpty &&
        pulled.state.order.isEmpty &&
        pulled.state.nextRemote == 2 &&
        ignored.actions.isEmpty &&
        ignored.state.nextRemote == 2 &&
        (committed.state.live.get? 2).isSome &&
        committed.state.nextRemote == 4 &&
        livePermits committed.actions == 0 &&
        acceptPermitIds committed.actions == [])
  | _ =>
    r.check "a pulled open waits for an explicit reservation" false
  let (pair, pairIds) ← require "openN" (openN 2 initiator [])
  let left := pairIds[0]!
  let right := pairIds[1]!
  let (busy, _) := admitAll pair left 1 [filled (testPayloadCap + 1) 2]
  let (fairState, _) := admitAll busy right 2 [byte 8]
  let (fair, fairActs) ← require "pumpN" (pumpN 3 fairState [])
  r.check "admitted streams take turns between chunks"
    (decide (chunkIds fairActs = [left, right, left]) &&
      decide (chunkTags fairActs = [1, 2, 1]) &&
      (chunkBytes fairActs)[0]?.map (·.size) == some testPayloadCap &&
      (chunkBytes fairActs)[1]?.map (·.size) == some 1 &&
      (chunkBytes fairActs)[2]?.map (·.size) == some 1 &&
      resolveCount 1 okW fairActs == 1 &&
      resolveCount 2 okW fairActs == 1 &&
      decide (writePermitIds fairActs = [right, left]) &&
      fair.admittedCount left == 0)
  r.check "the policy caps match the architecture table"
    (liveStreamCap == 32 && acceptBacklogCap == 16 && admittedWriteCap == 4)

/-- Accept-reservation ownership. The runtime channel holds each
envelope after `enqueueAccept`. These checks do not consult the
owner after it has exited. -/
private def runAccept (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let accepted ← require "openRemote" (State.openRemote initiator 2 true true)
  let reset ← require "resetRemote" (State.resetRemote accepted.state 2)
  r.check "reset before accept leaves the reservation with the envelope"
    (decide (enqueueIds accepted.actions = [2]) &&
      acceptPermitIds accepted.actions == [] &&
      acceptPermitIds reset.actions == [] &&
      (reset.state.live.get? 2).isNone &&
      reset.state.retired 2)
  let again ← require "openRemote" (State.openRemote initiator 2 true true)
  let half := State.halfClose again.state 2
  let finned ← require "acknowledged" (acknowledged (State.pump half.state))
  let closed ← require "finRemote" (State.finRemote finned.state 2)
  r.check "clean retirement before accept does not return the reservation"
    (decide (enqueueIds again.actions = [2]) &&
      acceptPermitIds finned.actions == [] &&
      acceptPermitIds closed.actions == [] &&
      (closed.state.live.get? 2).isNone)
  let first ← require "openRemote" (State.openRemote initiator 2 true true)
  let second ← require "openRemote" (State.openRemote first.state 4 true true)
  let resetSecond ← require "resetRemote" (State.resetRemote second.state 4)
  r.check "reset does not release either buffered accept"
    (decide (enqueueIds (first.actions ++ second.actions) = [2, 4]) &&
      acceptPermitIds resetSecond.actions == [] &&
      (resetSecond.state.live.get? 2).isSome &&
      (resetSecond.state.live.get? 4).isNone)
  let shut := State.claim second.state .ownerClose
  let againOwner := State.claim shut.state .ownerClose
  r.check "shutdown closes accept and leaves each envelope to its consumer"
    (decide (enqueueIds (first.actions ++ second.actions) = [2, 4]) &&
      acceptPermitIds shut.actions == [] &&
      tally closedAccept shut.actions == 1 &&
      againOwner.actions.isEmpty)
  r.check "accepted streams transfer in admission order"
    (decide (enqueueIds (first.actions ++ second.actions) = [2, 4]))
  let refused ← require "openRemote" (State.openRemote second.state 6 false false)
  let refusedAck ← require "ackSend" (State.ackSend refused.state)
  let reused ← require "openRemote" (State.openRemote refusedAck.state 8 true true)
  r.check "a missing accept permit refuses the id and the next permit admits the next id"
    (refused.state.outbound.isSome &&
      refused.state.nextRemote == 6 &&
      decide (enqueueIds refused.actions = []) &&
      acceptPermitIds refusedAck.actions == [] &&
      livePermits refusedAck.actions == 0 &&
      refusedAck.state.nextRemote == 8 &&
      decide (enqueueIds reused.actions = [8]) &&
      reused.state.outbound.isNone &&
      (reused.state.live.get? 8).isSome &&
      reused.state.nextRemote == 10)
  let held ← require "openRemote" (State.openRemote initiator 2 true false)
  let heldAck ← require "ackSend" (State.ackSend held.state)
  r.check "a refusal returns each acquired permit once and does not enqueue"
    (decide (enqueueIds held.actions = []) &&
      livePermits heldAck.actions == 1 &&
      acceptPermitIds heldAck.actions == [] &&
      heldAck.state.nextRemote == 4 &&
      isErr (State.ackSend heldAck.state) .noOutbound &&
      heldAck.state.outbound.isNone)

/-- Send intent, acknowledgement, and failure. -/
private def runSend (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let (opened, ids) ← require "openN" (openN 1 initiator [])
  let id := ids.head!
  let err := IO.userError "write"
  let big := filled (testPayloadCap + 3) 9
  let (large, _) := admitAll opened id 1 [big]
  let chunk := State.pump large
  let failedChunk ← require "failSend" (State.failSend chunk.state err)
  let later := State.claim failedChunk.state (.readerFault (IO.userError "later"))
  r.check "a failed non-final chunk resolves its tag once"
    (chunk.state.admittedCount id == 1 &&
      chunk.actions.length == 1 &&
      resolveCount 1 closedW failedChunk.actions == 1 &&
      resolveCount 1 okW failedChunk.actions == 0 &&
      decide (writePermitIds failedChunk.actions = [id]) &&
      livePermits failedChunk.actions == 1 &&
      decide (sentKinds failedChunk.actions = []) &&
      faultText failedChunk.state.cause == some "write" &&
      terminalText failedChunk.actions == some "write" &&
      later.actions.isEmpty &&
      faultText later.state.cause == some "write")
  let (one, _) := admitAll opened id 2 [byte 4]
  let finalIntent := State.pump one
  let failedFinal ← require "failSend" (State.failSend finalIntent.state err)
  r.check "a failed final chunk does not lose its write permit"
    (finalIntent.state.admittedCount id == 1 &&
      resolveCount 2 closedW failedFinal.actions == 1 &&
      resolveCount 2 okW failedFinal.actions == 0 &&
      decide (writePermitIds failedFinal.actions = [id]) &&
      livePermits failedFinal.actions == 1)
  let openIntent := State.openLocal initiator
  let failedOpen ← require "failSend" (State.failSend openIntent.state (IO.userError "open"))
  r.check "a failed open wakes the opener and returns the live permit"
    (openIntent.state.nextLocal == 1 &&
      (openIntent.state.live.get? 1).isNone &&
      decide (openErrors failedOpen.actions = [closedError]) &&
      livePermits failedOpen.actions == 1 &&
      failedOpen.state.nextLocal == 1 &&
      faultText failedOpen.state.cause == some "open" &&
      terminalText failedOpen.actions == some "open")
  let refuseIntent ← require "openRemote" (State.openRemote initiator 2 true false)
  let failedRefuse ← require "failSend" (State.failSend refuseIntent.state (IO.userError "refuse"))
  r.check "a failed refusal reset returns the acquired live permit once"
    (refuseIntent.state.nextRemote == 2 &&
      livePermits refuseIntent.actions == 0 &&
      failedRefuse.state.nextRemote == 2 &&
      livePermits failedRefuse.actions == 1 &&
      acceptPermitIds failedRefuse.actions == [] &&
      (State.claim failedRefuse.state .ownerClose).actions.isEmpty)
  let acceptRefuse ← require "openRemote" (State.openRemote initiator 2 false true)
  let failedAccept ← require "failSend" (State.failSend acceptRefuse.state (IO.userError "refuse-accept"))
  r.check "a failed refusal reset returns the acquired accept permit once"
    (decide (acceptPermitIds failedAccept.actions = [2]) &&
      livePermits failedAccept.actions == 0 &&
      failedAccept.state.nextRemote == 2 &&
      decide (enqueueIds acceptRefuse.actions = []))
  let (two, _) := admitAll opened id 3 [byte 1, byte 2]
  let resetIntent ← require "resetLocal" (State.resetLocal two id)
  let failedReset ← require "failSend" (State.failSend resetIntent.state (IO.userError "reset"))
  r.check "a failed local reset resolves each tag closed and sends no fin"
    ((resetIntent.state.live.get? id).isSome &&
      (resolutions resetIntent.actions).isEmpty &&
      resolveCount 3 closedW failedReset.actions == 1 &&
      resolveCount 4 closedW failedReset.actions == 1 &&
      resolveCount 3 resetW failedReset.actions == 0 &&
      resolveCount 4 resetW failedReset.actions == 0 &&
      decide (writePermitIds failedReset.actions = [id, id]) &&
      livePermits failedReset.actions == 1 &&
      portBeforeInbox failedReset.actions id .sessionClosed &&
      decide (sentKinds failedReset.actions = []))
  let (bare, bareIds) ← require "openN" (openN 1 initiator [])
  let bareId := bareIds.head!
  let half := State.halfClose bare bareId
  let finIntent := State.pump half.state
  let failedFin ← require "failSend" (State.failSend finIntent.state (IO.userError "fin"))
  r.check "a failed fin does not lose the live permit"
    ((finIntent.state.live.get? bareId).isSome &&
      livePermits finIntent.actions == 0 &&
      livePermits failedFin.actions == 1 &&
      decide (sentKinds failedFin.actions = []) &&
      (State.pump failedFin.state).actions.isEmpty)
  let (retiring, retIds) ← require "openN" (openN 1 initiator [])
  let retId := retIds.head!
  let readFin ← require "finRemote" (State.finRemote retiring retId)
  let halfRet := State.halfClose readFin.state retId
  let finRet := State.pump halfRet.state
  let failedRet ← require "failSend" (State.failSend finRet.state (IO.userError "fin-retire"))
  r.check "a failed retiring fin returns the live permit once"
    ((finRet.state.live.get? retId).isSome &&
      livePermits failedRet.actions == 1 &&
      decide (sentKinds failedRet.actions = []) &&
      acceptPermitIds failedRet.actions == [])
  let (queued, _) := admitAll opened id 8 [byte 8]
  let flushing := State.halfClose queued id
  let dataIntent := State.pump flushing.state
  let failedFlush ← require "failSend" (State.failSend dataIntent.state (IO.userError "flush"))
  r.check "no fin follows a failed data flush"
    (decide (sentKinds dataIntent.actions = [.data]) &&
      decide (sentKinds failedFlush.actions = []) &&
      (State.pump failedFlush.state).actions.isEmpty &&
      resolveCount 8 closedW failedFlush.actions == 1 &&
      resolveCount 8 okW failedFlush.actions == 0)
  let held ← require "openRemote" (State.openRemote initiator 2 true true)
  let (withWrite, _) := admitAll held.state 2 9 [byte 9]
  let send := State.pump withWrite
  let failedHeld ← require "failSend" (State.failSend send.state (IO.userError "accept-held"))
  let afterOwner := State.claim failedHeld.state .ownerClose
  r.check "a failed send does not return a transferred accept reservation"
    (decide (enqueueIds held.actions = [2]) &&
      acceptPermitIds failedHeld.actions == [] &&
      decide (writePermitIds failedHeld.actions = [2]) &&
      livePermits failedHeld.actions == 1 &&
      resolveCount 9 closedW failedHeld.actions == 1 &&
      afterOwner.actions.isEmpty)
  let openIntent := State.openLocal initiator
  let busy := State.openLocal openIntent.state
  let openedBusy ← require "ackSend" (State.ackSend busy.state)
  r.check "a local open during a send returns its permit and leaves the send"
    (isRunning busy.state.cause &&
      busy.state.outbound.isSome &&
      busy.state.nextLocal == 1 &&
      (busy.state.live.get? 1).isNone &&
      decide (openErrors busy.actions = [State.busyOpen]) &&
      livePermits busy.actions == 1 &&
      decide (openIds openedBusy.actions = [1]) &&
      livePermits openedBusy.actions == 0 &&
      openedBusy.state.outbound.isNone &&
      (openedBusy.state.live.get? 1).isSome)
  let (queued, _) := admitAll opened id 6 [byte 6]
  let sending := State.pump queued
  let s := sending.state
  let committed ← require "ackSend" (State.ackSend s)
  r.check "a reset during a send is sendInFlight and the write still commits once"
    (isErr (State.resetLocal s id) .sendInFlight &&
      isErr (State.openRemote s 2 true true) .sendInFlight &&
      isErr (State.resetRemote s id) .sendInFlight &&
      isErr (State.dataRemote s id [9]) .sendInFlight &&
      isErr (State.finRemote s id) .sendInFlight &&
      isErr (State.apply s dataFrame) .sendInFlight &&
      s.outbound.isSome &&
      s.nextRemote == 2 &&
      (s.live.get? 2).isNone &&
      s.admittedCount id == 1 &&
      resolveCount 6 okW committed.actions == 1 &&
      decide (writePermitIds committed.actions = [id]) &&
      committed.state.outbound.isNone &&
      isErr (State.ackSend committed.state) .noOutbound &&
      isErr (State.failSend committed.state err) .noOutbound)

private theorem resetNotData : Kind.reset ≠ Kind.data := by decide

private theorem finNotData : Kind.fin ≠ Kind.data := by decide

/-- Forged completions and scheduler violations. -/
private def runInvariant (r : Runner) : ExceptT String IO Unit := do
  let initiator := State.empty .initiator
  let (opened, ids) ← require "openN" (openN 1 initiator [])
  let id := ids.head!
  let diagnostics : List InvariantError := [
      .noOutbound, .sendAfterTerminal, .missingStream id, .emptyWriteQueue id,
      .writeTagMismatch id 9 1, .noRemainingChunk id, .openAlreadyLive id,
      .resetUnchanged id, .sendInFlight]
  r.check "toIOError carries the canonical invariant diagnostic"
    (diagnostics.all (fun e =>
        toString (InvariantError.toIOError e) == InvariantError.message e) &&
      InvariantError.message (.writeTagMismatch id 9 1) ==
        s!"mux: write tag mismatch {id} intent 9 queue 1" &&
      InvariantError.message .sendInFlight == "mux: send in flight" &&
      InvariantError.message .noOutbound == "mux: no outbound send" &&
      InvariantError.message .sendAfterTerminal ==
        "mux: send completion after the session ended")
  r.check "an acknowledgement or failure with no send keeps the session"
    (isErr (State.ackSend initiator) .noOutbound &&
      isErr (State.failSend initiator (IO.userError "none")) .noOutbound &&
      initiator.outbound.isNone &&
      initiator.nextLocal == 1 &&
      isRunning initiator.cause)
  let intent := State.openLocal initiator
  let ended := { intent.state with cause := .ownerClose }
  r.check "an acknowledgement after shutdown keeps the uncommitted open"
    (isErr (State.ackSend ended) .sendAfterTerminal &&
      isErr (State.failSend ended (IO.userError "late")) .sendAfterTerminal &&
      ended.outbound.isSome &&
      ended.nextLocal == 1 &&
      (ended.live.get? 1).isNone &&
      isOwnerClose ended.cause)
  let emptyQ := { opened with outbound := some (.chunk id 1 (byte 1) 0) }
  r.check "a chunk acknowledgement with an empty queue keeps the intent"
    (isErr (State.ackSend emptyQ) (.emptyWriteQueue id) &&
      emptyQ.outbound.isSome &&
      emptyQ.admittedCount id == 0)
  let gone := { opened with live := {}, order := #[], outbound := some (.chunk id 1 (byte 1) 0) }
  r.check "a chunk acknowledgement with no stream keeps the intent"
    (isErr (State.ackSend gone) (.missingStream id) &&
      gone.outbound.isSome &&
      (gone.live.get? id).isNone)
  let (queued, _) := admitAll opened id 1 [byte 1]
  let mismatch := { queued with outbound := some (.chunk id 9 (byte 1) 0) }
  r.check "a chunk acknowledgement with the wrong tag keeps the queue"
    (isErr (State.ackSend mismatch) (.writeTagMismatch id 9 1) &&
      mismatch.admittedCount id == 1 &&
      mismatch.outbound.isSome)
  if h : id ≠ 0 then
    let head? :=
      match queued.live.get? id with
      | some st => st.admitted[0]?
      | none => none
    let spent :=
      match queued.live.get? id, head? with
      | some st, some head =>
        let st' := { st with admitted := #[{ head with sent := head.bytes.size }] }
        { queued with
          live := queued.live.insert id st'
          outbound := some (.chunk id 1 head.bytes 0) }
      | _, _ => queued
    r.check "a chunk acknowledgement with no remaining bytes keeps the intent"
      (isErr (State.ackSend spent) (.noRemainingChunk id) &&
        spent.outbound.isSome &&
        spent.admittedCount id == 1)
    let liveOpen := {
      opened with outbound := some (.openStream id (Frame.ofControl .open id openNotData h)) }
    r.check "an open acknowledgement for a live id keeps that stream"
      (isErr (State.ackSend liveOpen) (.openAlreadyLive id) &&
        (liveOpen.live.get? id).isSome &&
        liveOpen.nextLocal == opened.nextLocal &&
        liveOpen.outbound.isSome)
    let resetStuck :=
      match opened.live.get? id with
      | some st =>
        { opened with
          live := opened.live.insert id { st with write := .sessionClosed }
          outbound := some (.reset id (Frame.ofControl .reset id resetNotData h)) }
      | none => opened
    r.check "a reset acknowledgement that cannot change the mode keeps the stream"
      (isErr (State.ackSend resetStuck) (.resetUnchanged id) &&
        resetStuck.writeMode? id == some .sessionClosed &&
        resetStuck.outbound.isSome &&
        isRunning resetStuck.cause)
    let noReset := {
      opened with
      live := {}
      order := #[]
      outbound := some (.reset id (Frame.ofControl .reset id resetNotData h)) }
    let noFin := {
      opened with
      live := {}
      order := #[]
      outbound := some (.fin id (Frame.ofControl .fin id finNotData h) 0) }
    r.check "a reset or fin acknowledgement with no stream keeps the intent"
      (isErr (State.ackSend noReset) (.missingStream id) &&
        isErr (State.ackSend noFin) (.missingStream id) &&
        noReset.outbound.isSome &&
        noFin.outbound.isSome &&
        (noReset.live.get? id).isNone)
  else
    r.check "a chunk acknowledgement with no remaining bytes keeps the intent" false
    r.check "an open acknowledgement for a live id keeps that stream" false
    r.check "a reset acknowledgement that cannot change the mode keeps the stream" false
    r.check "a reset or fin acknowledgement with no stream keeps the intent" false
  let (goodQ, _) := admitAll opened id 4 [byte 4]
  let good := State.pump goodQ
  let committed ← require "ackSend" (State.ackSend good.state)
  let failed ← require "failSend" (State.failSend good.state (IO.userError "once"))
  r.check "a valid acknowledgement commits once and a second completion is refused"
    (resolveCount 4 okW committed.actions == 1 &&
      committed.state.outbound.isNone &&
      isErr (State.ackSend committed.state) .noOutbound &&
      resolveCount 4 closedW failed.actions == 1 &&
      isErr (State.failSend failed.state (IO.userError "twice")) .noOutbound &&
      faultText failed.state.cause == some "once")

/-- Record an invariant error from one section, then continue the suite. -/
private def finish (r : Runner) (act : ExceptT String IO Unit) : IO Unit := do
  match ← act.run with
  | .ok () => pure ()
  | .error msg => r.check msg false

/-- The pure owner-loop transitions. -/
def run (r : Runner) : IO Unit := do
  r.section "mux test state" "packages/libp2p/mux/Libp2p/Mux/Test/State.lean"
  finish r (runIds r)
  finish r (runAdmission r)
  finish r (runWrites r)
  finish r (runLifecycle r)
  finish r (runTerminal r)
  finish r (runParser r)
  finish r (runAccept r)
  finish r (runSend r)
  finish r (runInvariant r)

end Tests.Mux.State

namespace Tests.Mux.Session

open Libp2p.Mux.Mock.Core
open Libp2p.Mux.Test.Session
open Libp2p.Mux.Test.State
open Libp2p.Mux.Test.Wire
open Conc
open Streams
open Streams.Mock.Multiformats
open Streams.Sim

private def pid : ProtocolId := ⟨"/leanp2p/test-mux/1.0.0"⟩

private def ma (s : String) : Async Multiaddr := do
  match Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

private structure Ends where
  dialer : Connection
  peer : Connection

private def ends (n : Nat) : Async Ends := do
  let net ← Net.new
  let l ← net.listen (← ma s!"/ip4/127.0.0.1/tcp/{4000 + n}")
  let some dialer ← net.dial l.addr | throw <| IO.userError "dial failed"
  let some peer ← l.accept | throw <| IO.userError "accept failed"
  return { dialer, peer }

private def drain (c : Connection) (owner : TaskSet) : BaseIO Unit := do
  owner.spawn do
    repeat
      match ← c.read with
      | none => break
      | some _ => pure ()

private theorem id1 : (1 : UInt32) ≠ 0 := by decide

private theorem openNotData : Kind.open ≠ Kind.data := by decide

private theorem resetNotData : Kind.reset ≠ Kind.data := by decide

private theorem finNotData : Kind.fin ≠ Kind.data := by decide

private def control (k : Kind) (hk : k ≠ Kind.data) : ByteArray :=
  Frame.encodeB (Frame.ofControl k 1 hk id1)

private def oneData (b : UInt8) : ByteArray :=
  Header.encodeB { kind := .data, streamId := 1, length := 1 } ++ ⟨#[b]⟩

private def isOk (r : Except Streams.Error Unit) : Bool :=
  match r with
  | .ok () => true
  | _ => false

private def isClosedW (r : Except Streams.Error Unit) : Bool :=
  match r with
  | .error .closed => true
  | _ => false

private def isResetW (r : Except Streams.Error Unit) : Bool :=
  match r with
  | .error .reset => true
  | _ => false

private def holdData (base : Connection) : BaseIO (Connection × Chan Unit) := do
  let hold ← Chan.new 1
  let conn : Connection := { base with
    write := fun bytes => do
      let openFrame :=
        match bytes[0]? with
        | some b => b == 1
        | none => false
      if openFrame then
        base.write bytes
      else
        match ← hold.recv with
        | none => throw <| IO.userError "write held"
        | some _ => base.write bytes }
  return (conn, hold)

private def mustOpen (sess : MuxSession) : Async Streams.Stream := do
  match ← (sess.openStream pid).run with
  | .ok stream => return stream
  | .error e => throw <| IO.userError s!"open failed: {repr e}"

/-- The text `join` throws, or `ok` when it returns. -/
private def joinText (sess : MuxSession) : Async String := do
  try
    let _ ← sess.join
    pure "ok"
  catch e =>
    pure e.toString

/-- Hook refs with the force flags clear unless a test sets them. -/
private def testHooks (invariant : Bool := false) (missing : Bool := false) :
    Async TestHooks := do
  return {
    registrySize := ← IO.mkRef 0
    forceInvariant := ← IO.mkRef invariant
    forceMissingPort := ← IO.mkRef missing
    acceptedEvent := ← IO.mkRef none
    appliedFrames := ← IO.mkRef 0
    captureOpenFrames := ← IO.mkRef none
    pauseAfterBudget := ← IO.mkRef none
    beforeOutcome := ← IO.mkRef none }

/-- Terminal-event order, teardown races, owner faults, and the port map. -/
private def runCorrections (r : Runner) : Async Unit := do
  -- EOF dequeued with a second chunk ready does not start that write.
  do
    let pair ← ends 15
    let hold : Chan Unit ← Chan.new 1
    let entered : Chan Unit ← Chan.new 1
    let accepted : Chan Unit ← Chan.new 1
    let phase ← IO.mkRef 0
    let conn : Connection := { pair.dialer with
      write := fun bytes => do
        let isData :=
          match bytes[0]? with
          | some b => b == 2
          | none => false
        if isData then
          let n ← phase.get
          phase.set (n + 1)
          if n == 0 then
            discard <| entered.send ()
            discard <| hold.recv
        pair.dialer.write bytes }
    let readGate : Chan Unit ← Chan.new 1
    let eofConn : Connection := { conn with
      read := do
        match ← readGate.recv with
        | none => return none
        | some _ => conn.read }
    let hooks ← testHooks
    let sess ← startWithHooks .initiator eofConn .empty hooks
    let stream ← mustOpen sess
    let writer ← TaskSet.new
    let wrote : Chan (Except Streams.Error Unit) ← Chan.new 1
    writer.spawn do
      let result ← stream.write ⟨Array.replicate (testPayloadCap + 1) 7⟩
      discard <| wrote.send result
    discard <| entered.recv
    -- The barrier waits for the reader's successful event post
    -- before the blocked write is released.
    hooks.acceptedEvent.set (some accepted)
    readGate.close
    match ← accepted.recv with
    | some _ => pure ()
    | none => throw <| IO.userError "the eof terminal was not accepted"
    hold.close
    writer.joinAll
    match ← wrote.recv with
    | some result =>
      r.check "no write starts after EOF is dequeued"
        ((← phase.get) == 1 && isClosedW result)
    | none => r.check "no write starts after EOF is dequeued" false
    match ← sess.join with
    | .ok () => r.check "EOF join stays a success" true
    | .error _ => r.check "EOF join stays a success" false

  -- A reader fault is dequeued before any later write can start.
  do
    let pair ← ends 16
    let hold : Chan Unit ← Chan.new 1
    let entered : Chan Unit ← Chan.new 1
    let accepted : Chan Unit ← Chan.new 1
    let phase ← IO.mkRef 0
    let boom := IO.userError "reader boom"
    let later := IO.userError "later write"
    let conn : Connection := { pair.dialer with
      write := fun bytes => do
        let isData :=
          match bytes[0]? with
          | some b => b == 2
          | none => false
        if isData then
          let n ← phase.get
          phase.set (n + 1)
          if n == 0 then
            discard <| entered.send ()
            discard <| hold.recv
          else
            throw later
        pair.dialer.write bytes }
    let readGate : Chan Unit ← Chan.new 1
    let faultConn : Connection := { conn with
      read := do
        match ← readGate.recv with
        | none => throw boom
        | some _ => conn.read }
    let hooks ← testHooks
    let sess ← startWithHooks .initiator faultConn .empty hooks
    let stream ← mustOpen sess
    let writer ← TaskSet.new
    let wrote : Chan (Except Streams.Error Unit) ← Chan.new 1
    writer.spawn do
      let result ← stream.write ⟨Array.replicate (testPayloadCap + 1) 7⟩
      discard <| wrote.send result
    discard <| entered.recv
    -- The barrier waits for the reader's successful event post
    -- before the blocked write is released.
    hooks.acceptedEvent.set (some accepted)
    readGate.close
    match ← accepted.recv with
    | some _ => pure ()
    | none => throw <| IO.userError "the reader fault was not accepted"
    hold.close
    writer.joinAll
    match ← wrote.recv with
    | some result =>
      r.check "no write starts after a reader fault is dequeued"
        ((← phase.get) == 1 && isClosedW result)
    | none => r.check "no write starts after a reader fault is dequeued" false
    let readerJoin ← joinText sess
    let readerAgain ← joinText sess
    r.check "the reader fault wins and join throws it" (readerJoin == boom.toString)
    r.check "a second join throws the same reader fault"
      (readerAgain == boom.toString)

  -- Opens and writes in flight at teardown all wake once.
  do
    let pair ← ends 17
    let hold : Chan Unit ← Chan.new 1
    let entered : Chan Unit ← Chan.new 1
    let conn : Connection := { pair.dialer with
      write := fun bytes => do
        let isData :=
          match bytes[0]? with
          | some b => b == 2
          | none => false
        if isData then
          discard <| entered.send ()
          match ← hold.recv with
          | none => throw <| IO.userError "write held"
          | some _ => pair.dialer.write bytes
        else
          pair.dialer.write bytes }
    let sess ← start .initiator conn
    let stream ← mustOpen sess
    let box : Chan Bool ← Chan.new 8
    let ready : Chan Unit ← Chan.new 7
    let workers ← TaskSet.new
    -- Pin the owner inside this write before the other callers run.
    workers.spawn do
      let result ← stream.write ⟨#[9]⟩
      discard <| box.send (isClosedW result)
    discard <| entered.recv
    for _ in List.range 3 do
      workers.spawn do
        discard <| ready.send ()
        let result ← stream.write ⟨#[9]⟩
        discard <| box.send (isClosedW result)
    for _ in List.range 4 do
      workers.spawn do
        discard <| ready.send ()
        match ← (sess.openStream pid).run with
        | .error e => discard <| box.send (e == closedError)
        | .ok extra =>
          extra.reset
          discard <| box.send false
    for _ in List.range 7 do
      discard <| ready.recv
    sess.close
    hold.close
    workers.joinAll
    let mut woke := 0
    for _ in List.range 8 do
      match ← box.recv with
      | some true => woke := woke + 1
      | _ => pure ()
    r.check "owner close answers every racing open and write" (woke == 8)
    match ← sess.join with
    | .ok () => r.check "owner close join stays a success" true
    | .error _ => r.check "owner close join stays a success" false

  -- The owner throws the invariant, then join reports that same error.
  do
    let pair ← ends 18
    let hooks ← testHooks true
    let sess ← startWithHooks .initiator pair.dialer .empty hooks
    let box : Chan Bool ← Chan.new 1
    let opener ← TaskSet.new
    opener.spawn do
      match ← (sess.openStream pid).run with
      | .error _ => discard <| box.send true
      | .ok extra =>
        extra.reset
        discard <| box.send false
    pair.peer.write ⟨#[1]⟩
    match ← box.recv with
    | some true => r.check "an owner invariant wakes the opener" true
    | _ => r.check "an owner invariant wakes the opener" false
    opener.joinAll
    let want := InvariantError.message .sendInFlight
    let ownerJoin ← joinText sess
    let ownerAgain ← joinText sess
    r.check "an owner invariant reaches join" (ownerJoin == want)
    r.check "a second join throws the same owner invariant" (ownerAgain == want)

  -- A missing port throws from the owner and join returns that text.
  do
    let pair ← ends 19
    let hooks ← testHooks false true
    let sess ← startWithHooks .initiator pair.dialer .empty hooks
    pair.peer.write ⟨#[1]⟩
    let missingJoin ← joinText sess
    let missingAgain ← joinText sess
    r.check "a missing port reaches join" (missingJoin == "mux: missing port 0")
    r.check "a second join throws the same missing port"
      (missingAgain == "mux: missing port 0")

  -- Retired handles stay usable, and the map keeps only live ports.
  do
    let pair ← ends 20
    let drainOwner ← TaskSet.new
    drain pair.peer drainOwner
    let hooks ← testHooks
    let sess ← startWithHooks .initiator pair.dialer .empty hooks
    let mut first : Option Streams.Stream := none
    let mut grew := false
    for i in List.range (liveStreamCap + 8) do
      let stream ← mustOpen sess
      if (← hooks.registrySize.get) != 1 then grew := true
      if i == 0 then first := some stream
      stream.reset
    let extra ← mustOpen sess
    r.check "the port map drops retired streams"
      (!grew && (← hooks.registrySize.get) == 1)
    match first with
    | some stream =>
      r.check "an old reset handle still reports reset"
        (isResetW (← stream.write ⟨#[1]⟩))
    | none => r.check "an old reset handle still reports reset" false
    extra.reset
    let _ ← mustOpen sess
    r.check "another open proceeds after the churn"
      ((← hooks.registrySize.get) == 1)
    sess.close
    discard <| sess.join
    drainOwner.joinAll

  -- Two joins wait together and both throw the stored owner error.
  do
    let pair ← ends 21
    let hooks ← testHooks true
    let sess ← startWithHooks .initiator pair.dialer .empty hooks
    let box : Chan Bool ← Chan.new 1
    let opener ← TaskSet.new
    opener.spawn do
      match ← (sess.openStream pid).run with
      | .error _ => discard <| box.send true
      | .ok extra =>
        extra.reset
        discard <| box.send false
    pair.peer.write ⟨#[1]⟩
    discard <| box.recv
    opener.joinAll
    let want := InvariantError.message .sendInFlight
    let answers : Chan String ← Chan.new 2
    let joins ← TaskSet.new
    joins.spawn do
      discard <| answers.send (← joinText sess)
    joins.spawn do
      discard <| answers.send (← joinText sess)
    joins.joinAll
    let left ← answers.recv
    let right ← answers.recv
    r.check "two concurrent joins throw the owner invariant"
      (left == some want && right == some want)

  -- Queued opens and writes are inside the channel. The pinned write
  -- throws, failSend claims the writer fault, and finishCause closes
  -- that still-open channel.
  do
    let pair ← ends 22
    let hold : Chan Unit ← Chan.new 1
    let entered : Chan Unit ← Chan.new 1
    let boom := IO.userError "writer boom"
    let conn : Connection := { pair.dialer with
      write := fun bytes => do
        let isData :=
          match bytes[0]? with
          | some b => b == 2
          | none => false
        if isData then
          discard <| entered.send ()
          match ← hold.recv with
          | none => throw boom
          | some _ => pair.dialer.write bytes
        else
          pair.dialer.write bytes }
    let accepted : Chan Unit ← Chan.new 7
    let hooks ← testHooks
    let sess ← startWithHooks .initiator conn .empty hooks
    let stream ← mustOpen sess
    let box : Chan Bool ← Chan.new 8
    let workers ← TaskSet.new
    workers.spawn do
      let result ← stream.write ⟨#[9]⟩
      discard <| box.send (isClosedW result)
    discard <| entered.recv
    hooks.acceptedEvent.set (some accepted)
    for _ in List.range 3 do
      workers.spawn do
        let result ← stream.write ⟨#[9]⟩
        discard <| box.send (isClosedW result)
    for _ in List.range 4 do
      workers.spawn do
        match ← (sess.openStream pid).run with
        | .error e => discard <| box.send (e == closedError)
        | .ok extra =>
          extra.reset
          discard <| box.send false
    for _ in List.range 7 do
      discard <| accepted.recv
    hold.close
    workers.joinAll
    let mut answered := 0
    for _ in List.range 8 do
      match ← box.recv with
      | some true => answered := answered + 1
      | _ => pure ()
    r.check "a writer fault drains every accepted open and write" (answered == 8)
    let writerJoin ← joinText sess
    let writerAgain ← joinText sess
    r.check "repeated joins throw that writer fault"
      (writerJoin == boom.toString && writerAgain == boom.toString)


/-- More than two parser budgets stay queued behind one local open. -/
private def runBudgetFairness (r : Runner) : Async Unit := do
  let pair ← ends 23
  let entered : Chan Unit ← Chan.new 1
  let release : Chan Unit ← Chan.new 1
  let accepted : Chan Unit ← Chan.new 1
  let hooks ← testHooks
  hooks.pauseAfterBudget.set (some { entered, release })
  let sess ← startWithHooks .initiator pair.dialer .empty hooks
  let mut blob : ByteArray := .empty
  for i in List.range (parserFrameBudget * 3) do
    discard <| mustOpen sess
    let id : UInt32 := 1 + 2 * UInt32.ofNat i
    let frame :=
      Header.encodeB { kind := .data, streamId := id, length := 1 } ++ ⟨#[7]⟩
    blob := blob ++ frame
  pair.peer.write blob
  discard <| entered.recv
  let saw : Chan Nat ← Chan.new 1
  hooks.captureOpenFrames.set (some saw)
  hooks.acceptedEvent.set (some accepted)
  let opener ← TaskSet.new
  opener.spawn do
    discard <| mustOpen sess
  discard <| accepted.recv
  discard <| release.send ()
  opener.joinAll
  match ← saw.recv with
  | some n =>
    r.check "a local open runs after one parser budget" (n == parserFrameBudget)
  | none => r.check "a local open runs after one parser budget" false
  sess.close
  discard <| sess.join

/-- Queued opens cannot hold a retained parser suffix. -/
private def runInverseFairness (r : Runner) : Async Unit := do
  let pair ← ends 30
  let entered : Chan Unit ← Chan.new 1
  let release : Chan Unit ← Chan.new 1
  let accepted : Chan Unit ← Chan.new 1
  let hooks ← testHooks
  hooks.pauseAfterBudget.set (some { entered, release })
  let sess ← startWithHooks .initiator pair.dialer .empty hooks
  let mut blob : ByteArray := .empty
  for i in List.range (parserFrameBudget * 3) do
    discard <| mustOpen sess
    let id : UInt32 := 1 + 2 * UInt32.ofNat i
    let frame :=
      Header.encodeB { kind := .data, streamId := id, length := 1 } ++ ⟨#[7]⟩
    blob := blob ++ frame
  pair.peer.write blob
  discard <| entered.recv
  let saw : Chan Nat ← Chan.new 4
  hooks.captureOpenFrames.set (some saw)
  hooks.acceptedEvent.set (some accepted)
  let openers ← TaskSet.new
  for _ in List.range 3 do
    openers.spawn do
      discard <| mustOpen sess
    discard <| accepted.recv
  discard <| release.send ()
  openers.joinAll
  let mut counts : List Nat := []
  for _ in List.range 3 do
    match ← saw.recv with
    | some n => counts := counts ++ [n]
    | none => counts := counts ++ [0]
  let want := [parserFrameBudget, parserFrameBudget * 2, parserFrameBudget * 3]
  r.check "queued opens advance one parser budget each" (counts == want)
  sess.close
  discard <| sess.join

/-- Caller events queued behind a deferred terminal cannot hold the parser. -/
private def runDeferredPressure (r : Runner) (n : Nat) (fault : Bool) : Async Unit := do
  let pair ← ends n
  let entered : Chan Unit ← Chan.new 1
  let release : Chan Unit ← Chan.new 1
  let readGate : Chan Unit ← Chan.new 1
  let accepted : Chan Unit ← Chan.new 1
  let phase ← IO.mkRef 0
  let reads ← IO.mkRef 0
  let boom := IO.userError "deferred reader boom"
  let conn : Connection := { pair.dialer with
    write := fun bytes => do
      let isData :=
        match bytes[0]? with
        | some b => b == 2
        | none => false
      if isData then
        phase.set ((← phase.get) + 1)
      pair.dialer.write bytes
    read := do
      let k ← reads.get
      reads.set (k + 1)
      if k == 0 then
        pair.dialer.read
      else if fault then
        match ← readGate.recv with
        | none => throw boom
        | some _ => pair.dialer.read
      else
        match ← readGate.recv with
        | none => return none
        | some _ => pair.dialer.read }
  let hooks ← testHooks
  hooks.pauseAfterBudget.set (some { entered, release })
  let sess ← startWithHooks .initiator conn .empty hooks
  let mut target : Option Streams.Stream := none
  let mut blob : ByteArray := .empty
  for i in List.range (parserFrameBudget * 4) do
    let stream ← mustOpen sess
    if i == 0 then target := some stream
    let id : UInt32 := 1 + 2 * UInt32.ofNat i
    let frame :=
      Header.encodeB { kind := .data, streamId := id, length := 1 } ++ ⟨#[7]⟩
    blob := blob ++ frame
  pair.peer.write blob
  discard <| entered.recv
  hooks.acceptedEvent.set (some accepted)
  readGate.close
  discard <| accepted.recv
  let enteredB : Chan Unit ← Chan.new 1
  let releaseB : Chan Unit ← Chan.new 1
  hooks.pauseAfterBudget.set (some { entered := enteredB, release := releaseB })
  discard <| release.send ()
  discard <| enteredB.recv
  let framesAtDefer ← hooks.appliedFrames.get
  let saw : Chan Nat ← Chan.new 4
  hooks.captureOpenFrames.set (some saw)
  let stream ← match target with
    | some stream => pure stream
    | none => throw <| IO.userError "pressure test opened no stream"
  let writers ← TaskSet.new
  let closed ← IO.mkRef true
  for _ in List.range 3 do
    writers.spawn do
      let result ← stream.write ⟨#[1]⟩
      if !(isClosedW result) then closed.set false
    discard <| accepted.recv
  let enteredC : Chan Unit ← Chan.new 1
  let releaseC : Chan Unit ← Chan.new 1
  hooks.pauseAfterBudget.set (some { entered := enteredC, release := releaseC })
  discard <| releaseB.send ()
  discard <| enteredC.recv
  let framesNext ← hooks.appliedFrames.get
  let firstRelease ← saw.recv
  let extra ← (saw.tryRecv : BaseIO (Option Nat))
  discard <| releaseC.send ()
  writers.joinAll
  let secondRelease ← saw.recv
  let chunks ← phase.get
  let answersClosed ← closed.get
  let stepOk :=
    framesAtDefer == parserFrameBudget * 2
      && framesNext == parserFrameBudget * 3
      && firstRelease == some (parserFrameBudget * 2)
      && extra == none
      && secondRelease == some (parserFrameBudget * 3)
      && chunks == 0
      && answersClosed
  if fault then
    let first ← joinText sess
    let second ← joinText sess
    r.check "a deferred reader fault advances under queued writes"
      (stepOk && first == boom.toString && second == boom.toString)
  else
    let first ← joinText sess
    let second ← joinText sess
    r.check "a deferred EOF advances under queued writes"
      (stepOk && first == "ok" && second == "ok")

/-- Retained complete frames, then EOF, a partial tail, or a reader fault. -/
private def runRetained (r : Runner) (n : Nat) (trailing fault : Bool) : Async Unit := do
  let pair ← ends n
  let entered : Chan Unit ← Chan.new 1
  let release : Chan Unit ← Chan.new 1
  let readGate : Chan Unit ← Chan.new 1
  let accepted : Chan Unit ← Chan.new 1
  let phase ← IO.mkRef 0
  let reads ← IO.mkRef 0
  let boom := IO.userError "retained reader boom"
  let conn : Connection := { pair.dialer with
    write := fun bytes => do
      let isData :=
        match bytes[0]? with
        | some b => b == 2
        | none => false
      if isData then
        phase.set ((← phase.get) + 1)
      pair.dialer.write bytes
    read := do
      let k ← reads.get
      reads.set (k + 1)
      if k == 0 then
        pair.dialer.read
      else if fault then
        match ← readGate.recv with
        | none => throw boom
        | some _ => pair.dialer.read
      else
        match ← readGate.recv with
        | none => return none
        | some _ => pair.dialer.read }
  let hooks ← testHooks
  hooks.pauseAfterBudget.set (some { entered, release })
  let sess ← startWithHooks .initiator conn .empty hooks
  let mut target : Option Streams.Stream := none
  let mut blob : ByteArray := .empty
  for i in List.range (parserFrameBudget * 3) do
    let stream ← mustOpen sess
    if i == 0 then target := some stream
    let id : UInt32 := 1 + 2 * UInt32.ofNat i
    let frame :=
      Header.encodeB { kind := .data, streamId := id, length := 1 } ++ ⟨#[7]⟩
    blob := blob ++ frame
  if trailing then blob := blob ++ ⟨#[0, 0, 0, 0]⟩
  pair.peer.write blob
  discard <| entered.recv
  let stream ← match target with
    | some stream => pure stream
    | none => throw <| IO.userError "retained test opened no stream"
  hooks.acceptedEvent.set (some accepted)
  let writer ← TaskSet.new
  writer.spawn do
    discard <| stream.write ⟨Array.replicate (testPayloadCap + 1) 7⟩
  discard <| accepted.recv
  readGate.close
  discard <| accepted.recv
  discard <| release.send ()
  writer.joinAll
  let chunks ← phase.get
  if fault then
    let first ← joinText sess
    let second ← joinText sess
    r.check "retained frames keep the reader fault"
      (first == boom.toString && second == boom.toString)
    r.check "no chunk follows a deferred reader fault" (chunks == 1)
  else if trailing then
    let once ← sess.join
    let twice ← sess.join
    match once, twice with
    | .error a, .error b =>
      r.check "a partial frame at EOF is a protocol error"
        (a == protocolPartial && b == protocolPartial)
    | _, _ => r.check "a partial frame at EOF is a protocol error" false
    r.check "no chunk follows a deferred partial EOF" (chunks == 1)
  else
    let first ← joinText sess
    let second ← joinText sess
    r.check "retained frames then EOF join as connection end"
      (first == "ok" && second == "ok")
    r.check "no chunk follows a deferred EOF" (chunks == 1)

/-- The second chunk of a large write leaves without a later event. -/
private def runSecondChunk (r : Runner) : Async Unit := do
  let pair ← ends 29
  let phase ← IO.mkRef 0
  let conn : Connection := { pair.dialer with
    write := fun bytes => do
      let isData :=
        match bytes[0]? with
        | some b => b == 2
        | none => false
      if isData then
        phase.set ((← phase.get) + 1)
      pair.dialer.write bytes }
  let sess ← start .initiator conn
  let stream ← mustOpen sess
  let wrote ← stream.write ⟨Array.replicate (testPayloadCap + 1) 7⟩
  let chunks ← phase.get
  r.check "a large write sends its second chunk" (isOk wrote && chunks == 2)
  sess.close
  discard <| sess.join

private def runArbitration (r : Runner) : Async Unit := do
  runBudgetFairness r
  runInverseFairness r
  runSecondChunk r
  runRetained r 24 false false
  runRetained r 25 true false
  runRetained r 26 false true
  runDeferredPressure r 31 false
  runDeferredPressure r 32 true
  -- A throwing transport close still closes the event channel.
  do
    let pair ← ends 27
    let hold : Chan Unit ← Chan.new 1
    let entered : Chan Unit ← Chan.new 1
    let conn : Connection := { pair.dialer with
      write := fun bytes => do
        let isData :=
          match bytes[0]? with
          | some b => b == 2
          | none => false
        if isData then
          discard <| entered.send ()
          match ← hold.recv with
          | none => throw <| IO.userError "write held"
          | some _ => pair.dialer.write bytes
        else
          pair.dialer.write bytes
      close := do
        pair.dialer.close
        throw <| IO.userError "close boom" }
    let sess ← start .initiator conn
    let stream ← mustOpen sess
    let box : Chan Bool ← Chan.new 1
    let workers ← TaskSet.new
    workers.spawn do
      let result ← stream.write ⟨#[9]⟩
      discard <| box.send (isClosedW result)
    discard <| entered.recv
    let returned ← try
      sess.close
      pure true
    catch _ =>
      pure false
    r.check "close returns when the transport close throws" returned
    match ← (sess.openStream pid).run with
    | .error e => r.check "close shuts the event channel" (e == closedError)
    | .ok extra =>
      extra.reset
      r.check "close shuts the event channel" false
    hold.close
    workers.joinAll
    match ← box.recv with
    | some true => r.check "a pinned writer wakes after a throwing close" true
    | _ => r.check "a pinned writer wakes after a throwing close" false
    let first ← joinText sess
    let second ← joinText sess
    r.check "repeated joins stay an owner close" (first == "ok" && second == "ok")
  -- The reader fault has won. Close during the outcome pause keeps it.
  do
    let pair ← ends 28
    let entered : Chan Unit ← Chan.new 1
    let release : Chan Unit ← Chan.new 1
    let hooks ← testHooks
    hooks.beforeOutcome.set (some { entered, release })
    let boom := IO.userError "reader boom"
    let conn : Connection := { pair.dialer with
      read := throw boom }
    let sess ← startWithHooks .initiator conn .empty hooks
    discard <| entered.recv
    sess.close
    discard <| release.send ()
    let first ← joinText sess
    let second ← joinText sess
    r.check "a later close keeps the winning reader fault"
      (first == boom.toString && second == boom.toString)

private def checks (r : Runner) : Async Unit := do
  -- Startup, join, and a second join.
  do
    let pair ← ends 1
    let sess ← start .initiator pair.dialer
    sess.close
    match ← sess.join with
    | .ok () => r.check "startup and clean shutdown join once" true
    | .error _ => r.check "startup and clean shutdown join once" false
    match ← sess.join with
    | .ok () => r.check "a second join returns the same success" true
    | .error _ => r.check "a second join returns the same success" false
    match ← pair.peer.read with
    | none => r.check "closing the session ends the peer read" true
    | some _ => r.check "closing the session ends the peer read" false

  -- One acknowledged data frame.
  do
    let pair ← ends 2
    let sess ← start .initiator pair.dialer
    let stream ← mustOpen sess
    let wrote ← stream.write ⟨#[9]⟩
    let openBytes ← pair.peer.readExactly 9
    let dataBytes ← pair.peer.readExactly 10
    let payloadOk :=
      match dataBytes with
      | some (frame, rest) =>
        frame.size == 10 && frame[9]? == some 9 && rest.isEmpty
      | none => false
    r.check "one outbound data frame is written and acknowledged"
      (isOk wrote && openBytes.isSome && payloadOk)
    sess.close
    match ← sess.join with
    | .ok () => r.check "the reader and the owner both join" true
    | .error _ => r.check "the reader and the owner both join" false

  -- A failed write keeps the IO.Error.
  do
    let pair ← ends 3
    let boom := IO.userError "boom"
    let conn : Connection := { pair.dialer with write := fun _ => throw boom }
    let sess ← start .initiator conn
    match ← (sess.openStream pid).run with
    | .ok _ => r.check "a failed open write resolves closed" false
    | .error e =>
      r.check "a failed open write resolves closed" (e == closedError)
    let first ← joinText sess
    let second ← joinText sess
    r.check "a failed connection write keeps its IO.Error" (first == boom.toString)
    r.check "a second join throws the same connection error" (second == boom.toString)

  -- Malformed bytes are a protocol failure.
  do
    let pair ← ends 4
    let sess ← start .initiator pair.dialer
    pair.peer.write ⟨#[0, 0, 0, 0, 1, 0, 0, 0, 0]⟩
    match ← sess.join with
    | .error e =>
      r.check "a malformed frame is a protocol failure" (e == protocolMalformed)
    | .ok () =>
      r.check "a malformed frame is a protocol failure" false

  -- A frame split across reads.
  do
    let pair ← ends 5
    let sess ← start .initiator pair.dialer
    let stream ← mustOpen sess
    let _ ← pair.peer.readExactly 9
    let frame := oneData 7
    pair.peer.write (frame.extract 0 4)
    pair.peer.write (frame.extract 4 frame.size)
    match ← stream.read with
    | .ok (some chunk) =>
      r.check "a frame split across reads is delivered" (chunk == ⟨#[7]⟩)
    | _ => r.check "a frame split across reads is delivered" false
    sess.close
    discard <| sess.join

  -- A payload that crosses the reader's slice boundary.
  do
    let pair ← ends 14
    let sess ← start .initiator pair.dialer
    let stream ← mustOpen sess
    let _ ← pair.peer.readExactly 9
    let payload : ByteArray := ⟨Array.replicate testPayloadCap 7⟩
    let frame :=
      Header.encodeB {
        kind := .data
        streamId := 1
        length := UInt32.ofNat testPayloadCap } ++ payload
    pair.peer.write frame
    match ← stream.read with
    | .ok (some chunk) =>
      r.check "a frame that crosses a slice boundary is delivered" (chunk == payload)
    | _ =>
      r.check "a frame that crosses a slice boundary is delivered" false
    sess.close
    discard <| sess.join

  -- More frames than one parser budget arrive in one read.
  -- Each frame belongs to a different stream.
  do
    let pair ← ends 6
    let reads ← IO.mkRef 0
    let conn : Connection := { pair.dialer with
      read := do
        reads.modify (· + 1)
        pair.dialer.read }
    let sess ← start .initiator conn
    let mut burst : Array Streams.Stream := #[]
    for _ in List.range 10 do
      burst := burst.push (← mustOpen sess)
    let mut bulk : ByteArray := .empty
    for i in List.range 10 do
      let id := UInt32.ofNat (1 + 2 * i)
      bulk := bulk ++ Header.encodeB {
        kind := .data
        streamId := id
        length := 1 } ++ ⟨#[UInt8.ofNat i]⟩
    pair.peer.write bulk
    let mut got : Array UInt8 := #[]
    for stream in burst do
      match ← stream.read with
      | .ok (some chunk) =>
        match chunk[0]? with
        | some b => got := got.push b
        | none => pure ()
      | _ => pure ()
    let n ← reads.get
    r.check "a budget of frames drains without a read per frame"
      (got == (List.range 10).toArray.map UInt8.ofNat && 1 ≤ n && n ≤ 3)
    sess.close
    discard <| sess.join

  -- Reset publishes the port before it closes admission.
  do
    let pair ← ends 7
    let sess ← start .initiator pair.dialer
    let stream ← mustOpen sess
    let _ ← pair.peer.readExactly 9
    pair.peer.write (control .reset resetNotData)
    match ← stream.read with
    | .error .reset =>
      let mut resetCount := 0
      for _ in List.range 5 do
        if isResetW (← stream.write ⟨#[1]⟩) then
          resetCount := resetCount + 1
      r.check "five writes after reset observe the reset port" (resetCount == 5)
    | _ => r.check "five writes after reset observe the reset port" false
    sess.close
    discard <| sess.join

  -- A reset frame write wakes a blocked fifth writer after the port update.
  do
    let pair ← ends 12
    let drainOwner ← TaskSet.new
    drain pair.peer drainOwner
    let gate : Chan Unit ← Chan.new 1
    let conn : Connection := { pair.dialer with
      write := fun bytes => do
        let openFrame :=
          match bytes[0]? with
          | some b => b == 1
          | none => false
        if openFrame then
          pair.dialer.write bytes
        else
          let _ ← gate.recv
          pair.dialer.write bytes }
    let sess ← start .initiator conn
    let stream ← mustOpen sess
    stream.reset
    let box ← Chan.new 5
    let writers ← TaskSet.new
    for _ in List.range 5 do
      writers.spawn do
        let result ← stream.write ⟨#[3]⟩
        discard <| box.send result
    gate.close
    writers.joinAll
    let mut resetCount := 0
    for _ in List.range 5 do
      match ← box.recv with
      | some result =>
        if isResetW result then resetCount := resetCount + 1
      | none => pure ()
    r.check "a blocked fifth writer wakes with reset" (resetCount == 5)
    sess.close
    discard <| sess.join
    drainOwner.joinAll

  -- Negotiation bytes are frames before the first read.
  do
    let pair ← ends 13
    let sess ← start .responder pair.dialer (control .open openNotData)
    match ← sess.accept with
    | some _ => r.check "a leftover open frame is accepted" true
    | none => r.check "a leftover open frame is accepted" false
    sess.close
    discard <| sess.join

  -- Half-close closes admission.
  do
    let pair ← ends 8
    let drainOwner ← TaskSet.new
    drain pair.peer drainOwner
    let sess ← start .initiator pair.dialer
    let stream ← mustOpen sess
    stream.close
    let wrote ← stream.write ⟨#[1]⟩
    r.check "a write after half-close completes with closed" (isClosedW wrote)
    sess.close
    discard <| sess.join
    drainOwner.joinAll

  -- Five writers wake on shutdown.
  do
    let pair ← ends 9
    let (conn, hold) ← holdData pair.dialer
    let sess ← start .initiator conn
    let stream ← mustOpen sess
    let box ← Chan.new 5
    let writers ← TaskSet.new
    for _ in List.range 5 do
      writers.spawn do
        let result ← stream.write ⟨#[3]⟩
        discard <| box.send result
    sess.close
    hold.close
    writers.joinAll
    let mut closedCount := 0
    for _ in List.range 5 do
      match ← box.recv with
      | some result =>
        if isClosedW result then closedCount := closedCount + 1
      | none => pure ()
    r.check "five blocked writers wake with closed on shutdown" (closedCount == 5)
    match ← sess.join with
    | .ok () => r.check "shutdown join stays a success" true
    | .error _ => r.check "shutdown join stays a success" false

  -- Accept envelopes survive reset.
  do
    let pair ← ends 10
    let sess ← start .responder pair.dialer
    pair.peer.write (control .open openNotData)
    pair.peer.write (control .reset resetNotData)
    match ← sess.accept with
    | none => r.check "an accepted stream survives reset" false
    | some stream =>
      match ← stream.read with
      | .error .reset =>
        r.check "an accepted stream survives reset" true
      | _ => r.check "an accepted stream survives reset" false
    sess.close
    discard <| sess.join

  -- Live permits return, so the cap can be filled twice.
  do
    let pair ← ends 11
    let drainOwner ← TaskSet.new
    drain pair.peer drainOwner
    let sess ← start .initiator pair.dialer
    let mut streams : Array Streams.Stream := #[]
    for _ in List.range liveStreamCap do
      streams := streams.push (← mustOpen sess)
    for stream in streams do
      stream.reset
    let extra ← mustOpen sess
    extra.reset
    r.check "a live permit returns and another open proceeds" true
    sess.close
    discard <| sess.join
    drainOwner.joinAll

  runCorrections r
  runArbitration r

/-- The runtime shell over the sim connection. -/
def run (r : Runner) : IO Unit := do
  r.section "mux test session" "packages/libp2p/mux/Libp2p/Mux/Test/Session.lean"
  Async.run (checks r)

end Tests.Mux.Session

namespace Tests.Mux.Public

open Libp2p.Mux
open Libp2p.Mux.Mock.Core
open Libp2p.Mux.Test.Wire
open Conc
open Streams
open Streams.Mock.Multiformats
open Streams.Sim

private structure Ends where
  dialer : Connection
  peer : Connection

private def ends (n : Nat) : Async Ends := do
  let net ← Net.new
  let addr ← match Multiaddr.parse? s!"/ip4/127.0.0.1/tcp/{4000 + n}" with
    | .ok a => pure a
    | .error _ => throw <| IO.userError s!"test address {n} does not parse"
  let l ← net.listen addr
  let some dialer ← net.dial l.addr | throw <| IO.userError "dial failed"
  let some peer ← l.accept | throw <| IO.userError "accept failed"
  return { dialer, peer }

/-- The session `Mux.test.open` returns. -/
private def openSession (role : Role) (conn : Connection)
    (leftover : ByteArray := .empty) : Async MuxSession := do
  match ← (test.open role conn leftover).run with
  | .ok sess => return sess
  | .error e => throw <| IO.userError s!"public open failed: {repr e}"

private def readPayload (stream : Stream) : Async ByteArray := do
  match ← stream.read with
  | .ok (some bytes) => return bytes
  | .ok none => throw <| IO.userError "public read ended"
  | .error e => throw <| IO.userError s!"public read failed: {repr e}"

private def takeHeader (c : Connection) (pending : ByteArray) :
    Async (Header × ByteArray) := do
  match ← c.readExactly headerSize pending with
  | none => throw <| IO.userError "header ended"
  | some (frame, rest) =>
    match Header.decodeB? frame with
    | .ok (h, suffix) =>
      if suffix.isEmpty then return (h, rest)
      else throw <| IO.userError "header left a suffix"
    | .error _ => throw <| IO.userError "header did not decode"

private def openFrame (id : UInt32) : ByteArray :=
  Header.encodeB { kind := .open, streamId := id, length := 0 }

private def dataFrame (id : UInt32) (b : UInt8) : ByteArray :=
  Header.encodeB { kind := .data, streamId := id, length := 1 } ++ ⟨#[b]⟩

/-- Two concurrent opens. The peer reads both open frames. -/
private def runParity (r : Runner) (n : Nat) (role : Role)
    (low high : UInt32) (title : String) : Async Unit := do
  let pair ← ends n
  let sess ← openSession role pair.dialer
  let other : ProtocolId := ⟨"/leanp2p/not-on-wire/1"⟩
  let workers ← TaskSet.new
  workers.spawn do
    match ← (sess.openStream testId).run with
    | .ok _ => pure ()
    | .error e => throw <| IO.userError s!"open failed: {repr e}"
  workers.spawn do
    match ← (sess.openStream other).run with
    | .ok _ => pure ()
    | .error e => throw <| IO.userError s!"open failed: {repr e}"
  workers.joinAll
  let (h1, pending) ← takeHeader pair.peer .empty
  let (h2, _) ← takeHeader pair.peer pending
  let ids := (h1.streamId, h2.streamId)
  let framesOk :=
    (ids == (low, high) || ids == (high, low))
      && h1.kind == Kind.open && h2.kind == Kind.open
      && h1.length == 0 && h2.length == 0
  r.check title framesOk
  sess.close
  discard <| sess.join

/-- One public open, then bytes in both directions. -/
private def runRoundTrip (r : Runner) : Async Unit := do
  let pair ← ends 42
  let dial ← openSession .initiator pair.dialer
  let peer ← openSession .responder pair.peer
  match ← (dial.openStream testId).run with
  | .error _ =>
    r.check "the peer accepts a public open" false
    r.check "bytes round-trip in both directions" false
  | .ok outbound =>
    let wrote ← outbound.write ⟨#[7]⟩
    match ← peer.accept with
    | none =>
      r.check "the peer accepts a public open" false
      r.check "bytes round-trip in both directions" false
    | some remote =>
      r.check "the peer accepts a public open" true
      let got ← readPayload remote
      let replied ← remote.write ⟨#[8]⟩
      let back ← readPayload outbound
      let wroteOk :=
        match wrote with
        | .ok () => true
        | .error _ => false
      let repliedOk :=
        match replied with
        | .ok () => true
        | .error _ => false
      r.check "bytes round-trip in both directions"
        (wroteOk && repliedOk && got == ⟨#[7]⟩ && back == ⟨#[8]⟩)
  dial.close
  peer.close
  discard <| dial.join
  discard <| peer.join

/-- Leftover bytes are the reader's first input. -/
private def runLeftover (r : Runner) : Async Unit := do
  let pair ← ends 43
  let leftover := openFrame 2 ++ dataFrame 2 1
  let later := openFrame 4 ++ dataFrame 4 2
  pair.peer.write later
  let sess ← openSession .initiator pair.dialer leftover
  match ← sess.accept with
  | none => r.check "a leftover arrives before later connection bytes" false
  | some first =>
    match ← sess.accept with
    | none => r.check "a leftover arrives before later connection bytes" false
    | some second =>
      let early ← readPayload first
      let next ← readPayload second
      r.check "a leftover arrives before later connection bytes"
        (early == ⟨#[1]⟩ && next == ⟨#[2]⟩)
  sess.close
  discard <| sess.join

/-- Two public closes. `accept` returns `none`, both joins succeed, and the peer read ends. -/
private def runClose (r : Runner) : Async Unit := do
  let pair ← ends 44
  let sess ← openSession .initiator pair.dialer
  sess.close
  sess.close
  match ← sess.accept with
  | none => r.check "accept after repeated public close returns none" true
  | some stream =>
    stream.reset
    r.check "accept after repeated public close returns none" false
  match ← sess.join with
  | .ok () => r.check "repeated public close joins once" true
  | .error _ => r.check "repeated public close joins once" false
  match ← sess.join with
  | .ok () => r.check "a second join after repeated close succeeds" true
  | .error _ => r.check "a second join after repeated close succeeds" false
  match ← pair.peer.read with
  | none => r.check "repeated public close ends the peer read" true
  | some _ => r.check "repeated public close ends the peer read" false

/-- The first open id from one fresh public session, after a clean join. -/
private def firstOpenId (n : Nat) (role : Role) : Async (Option UInt32) := do
  let pair ← ends n
  let sess ← openSession role pair.dialer
  let id ←
    match ← (sess.openStream testId).run with
    | .error _ => pure (none : Option UInt32)
    | .ok _ =>
      let (h, _) ← takeHeader pair.peer .empty
      if h.kind == Kind.open && h.length == 0 then
        pure (some h.streamId)
      else
        pure none
  sess.close
  match ← sess.join with
  | .ok () => return id
  | .error _ => return none

/-- Two fresh sessions of one role both issue that role's first id. -/
private def runIdRestart (r : Runner) : Async Unit := do
  let initiatorA ← firstOpenId 45 .initiator
  let initiatorB ← firstOpenId 46 .initiator
  r.check "two initiator sessions both open stream id 1"
    (initiatorA == some 1 && initiatorB == some 1)
  let responderA ← firstOpenId 47 .responder
  let responderB ← firstOpenId 48 .responder
  r.check "two responder sessions both open stream id 2"
    (responderA == some 2 && responderB == some 2)

/-- Both ends open together. Each accepts the other stream and reads its payload. -/
private def runConcurrentOpens (r : Runner) : Async Unit := do
  let pair ← ends 49
  let initiator ← openSession .initiator pair.dialer
  let responder ← openSession .responder pair.peer
  let initiatorOpen : Chan (Except Mock.Core.Error Stream) ← Chan.new 1
  let responderOpen : Chan (Except Mock.Core.Error Stream) ← Chan.new 1
  let workers ← TaskSet.new
  workers.spawn do
    let result ← (initiator.openStream testId).run
    match ← initiatorOpen.send result with
    | .ok () => pure ()
    | .error _ => throw <| IO.userError "initiator open result was not delivered"
  workers.spawn do
    let result ← (responder.openStream testId).run
    match ← responderOpen.send result with
    | .ok () => pure ()
    | .error _ => throw <| IO.userError "responder open result was not delivered"
  workers.joinAll
  match ← initiatorOpen.recv, ← responderOpen.recv with
  | some (.ok openedByInitiator), some (.ok openedByResponder) =>
    r.check "both ends open a stream together" true
    match ← initiator.accept, ← responder.accept with
    | some acceptedByInitiator, some acceptedByResponder =>
      r.check "each end accepts the opposite open" true
      let wroteInitiator ← openedByInitiator.write ⟨#[3]⟩
      let wroteResponder ← openedByResponder.write ⟨#[4]⟩
      let gotResponder ← acceptedByResponder.read
      let gotInitiator ← acceptedByInitiator.read
      let initiatorOk :=
        match wroteInitiator with
        | .ok () => true
        | .error _ => false
      let responderOk :=
        match wroteResponder with
        | .ok () => true
        | .error _ => false
      let readResponder :=
        match gotResponder with
        | .ok (some bytes) => bytes == ⟨#[3]⟩
        | _ => false
      let readInitiator :=
        match gotInitiator with
        | .ok (some bytes) => bytes == ⟨#[4]⟩
        | _ => false
      r.check "concurrent streams carry distinct payloads"
        (initiatorOk && responderOk && readResponder && readInitiator)
    | _, _ =>
      r.check "each end accepts the opposite open" false
      r.check "concurrent streams carry distinct payloads" false
  | some (.error _), _
  | _, some (.error _)
  | none, _
  | _, none =>
    r.check "both ends open a stream together" false
    r.check "each end accepts the opposite open" false
    r.check "concurrent streams carry distinct payloads" false
  initiator.close
  responder.close
  match ← initiator.join, ← responder.join with
  | .ok (), .ok () => r.check "both public sessions join after the exchange" true
  | _, _ => r.check "both public sessions join after the exchange" false

/-- A reader fault through `Mux.test.open` stays the connection `IO.Error`.
Both joins throw that same error. -/
private def runReaderFault (r : Runner) : Async Unit := do
  let pair ← ends 50
  let boom := IO.userError "reader boom"
  -- The reader parks on this gate. Closing it throws after `open` returns.
  let gate : Chan Unit ← Chan.new 1
  let conn : Connection := { pair.dialer with
    read := do
      match ← gate.recv with
      | none => throw boom
      | some _ => pair.dialer.read }
  match ← (test.open .initiator conn .empty).run with
  | .error _ =>
    gate.close
    pair.dialer.close
    pair.peer.close
    r.check "Mux.test.open returns before the reader fault" false
    r.check "the public reader fault is the connection error" false
    r.check "a second public join throws the same reader fault" false
  | .ok sess =>
    r.check "Mux.test.open returns before the reader fault" true
    gate.close
    let first ←
      try
        match ← sess.join with
        | .ok () => pure "returned ok"
        | .error _ => pure "returned core error"
      catch e =>
        pure e.toString
    let second ←
      try
        match ← sess.join with
        | .ok () => pure "returned ok"
        | .error _ => pure "returned core error"
      catch e =>
        pure e.toString
    r.check "the public reader fault is the connection error" (first == boom.toString)
    r.check "a second public join throws the same reader fault"
      (second == boom.toString && second == first)
    pair.peer.close

/-- A kind-zero peer header through `Mux.test.open`.
Both joins return the same protocol error. -/
private def runMalformed (r : Runner) : Async Unit := do
  let pair ← ends 51
  match ← (test.open .initiator pair.dialer .empty).run with
  | .error _ =>
    pair.dialer.close
    pair.peer.close
    r.check "a public malformed frame returns a protocol error" false
    r.check "a second public join returns the same protocol error" false
  | .ok sess =>
    let observed : Except IO.Error
        (Except Mock.Core.Error Unit × Except Mock.Core.Error Unit) ←
      try
        pair.peer.write ⟨#[0, 0, 0, 0, 1, 0, 0, 0, 0]⟩
        pure (.ok (← sess.join, ← sess.join))
      catch e =>
        pure (.error e)
    pair.peer.close
    match observed with
    | .error e => throw e
    | .ok (first, second) =>
      match first, second with
      | .error e1, .error e2 =>
        let firstProtocol :=
          match e1 with
          | .protocol _ => true
          | _ => false
        let secondProtocol :=
          match e2 with
          | .protocol _ => true
          | _ => false
        r.check "a public malformed frame returns a protocol error" firstProtocol
        r.check "a second public join returns the same protocol error"
          (secondProtocol && decide (e1 = e2))
      | _, _ =>
        r.check "a public malformed frame returns a protocol error" false
        r.check "a second public join returns the same protocol error" false

private def checks (r : Runner) : Async Unit := do
  r.check "Mux.test.id is Mux.testId" (decide (test.id = testId))
  r.check "the test protocol id is /leanp2p/test-mux/1.0.0"
    (test.id.toString == "/leanp2p/test-mux/1.0.0")
  runParity r 40 .initiator 1 3 "an initiator open pair uses distinct odd ids"
  runParity r 41 .responder 2 4 "a responder open pair uses distinct even ids"
  runRoundTrip r
  runLeftover r
  runClose r
  runIdRestart r
  runConcurrentOpens r
  runReaderFault r
  runMalformed r

/-- The public `Mux.test` boundary over the sim connection. -/
def run (r : Runner) : IO Unit := do
  r.section "mux test value" "packages/libp2p/mux/Libp2p/Mux/Test.lean"
  Async.run (checks r)

/-- The public reader-fault path through `Mux.test.open`. -/
def runFault (r : Runner) : IO Unit := do
  r.section "mux test value" "packages/libp2p/mux/Libp2p/Mux/Test.lean"
  Async.run (runReaderFault r)

/-- The public malformed-frame path through `Mux.test.open`. -/
def runHostile (r : Runner) : IO Unit := do
  r.section "mux test value" "packages/libp2p/mux/Libp2p/Mux/Test.lean"
  Async.run (runMalformed r)

end Tests.Mux.Public

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
  Mux.Seam.run r
  Mux.State.run r
  Mux.Session.run r
  Mux.Public.run r

end Tests
