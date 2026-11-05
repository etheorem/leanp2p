import Tests.Support
import Bytes
import Snappy

/-!
# Snappy raw blocks (unit W6.2, Phases 3A through 4B)

Compression and bounded decompression against `google/snappy` 1.3.1.
The empty block and `hello hello hello hello` use the bytes pinned by
`native/check/core.cpp`. Phase 4A adds small malformed blocks and cap
rejections. Phase 4B reads the Go v0.0.4 raw-block fixture, round-trips
deterministic inputs through the public API, and repeats short calls.
The later checks repeat a public round trip, walk the `EmitCopy`
lengths, reject a framed-stream identifier, and call the compression
size predicate. Each borrowed input is snapshotted as a `List Nat`
before the extern call.
-/

set_option autoImplicit false

namespace Tests

open Bytes
open Lean (Json)

/--
Read the input bytes after `result` exists.
The result argument keeps this read after the extern call. `before` is
a `List Nat`, so it is a separate value from the borrowed `ByteArray`.
-/
@[noinline]
private def bytesAfter (result : Except Snappy.Error ByteArray) (input : ByteArray) : List Nat :=
  match result with
  | .ok _ => toNatList input
  | .error _ => toNatList input

/--
Materialize the input bytes, compress, then read the input bytes again.
-/
@[noinline]
private def snapshotAndCompress (input : ByteArray) :
    List Nat × List Nat × Except Snappy.Error ByteArray :=
  let before := toNatList input
  let result := Snappy.compress input
  let after := bytesAfter result input
  (before, after, result)

/-- Parse a fixture. A malformed hex string fails the named check. -/
private def parsedHex (r : Runner) (name hex : String) : IO (Option ByteArray) := do
  match ofHex? hex with
  | some bytes => return some bytes
  | none =>
    r.check s!"{name} fixture hex" false
    return none

/--
Check one compression, a second compression of the same input, and
the borrowed bytes after both calls.
-/
private def checkCase (r : Runner) (name : String) (input : ByteArray)
    (accept : ByteArray → Bool) : IO Unit := do
  let (before, after, result) := snapshotAndCompress input
  let again := Snappy.compress input
  let afterAgain := bytesAfter again input
  r.check s!"{name} input unchanged" (before == after && before == afterAgain)
  match result, again with
  | .ok out, .ok repeated =>
    r.check s!"{name} output" (accept out)
    r.check s!"{name} repeat" (out == repeated)
  | _, _ =>
    r.check s!"{name} compresses" false

/-- The output bytes equal the parsed fixture. -/
private def checkExact (r : Runner) (name : String) (input : ByteArray)
    (hex : String) : IO Unit := do
  match ← parsedHex r name hex with
  | none => return
  | some expected =>
    checkCase r name input fun out => out == expected

/-- The output is one nonempty raw block. -/
private def checkNonempty (r : Runner) (name : String) (input : ByteArray) : IO Unit := do
  checkCase r name input fun out => !out.isEmpty

/--
Materialize the compressed bytes, decompress, then read those bytes again.
-/
@[noinline]
private def snapshotAndDecompress (input : ByteArray) (cap : Nat) :
    List Nat × List Nat × Except Snappy.Error ByteArray :=
  let before := toNatList input
  let result := Snappy.decompress input cap
  let after := bytesAfter result input
  (before, after, result)

/-- Check one decompression and the borrowed compressed bytes. -/
private def checkDecompress (r : Runner) (name : String) (input : ByteArray)
    (cap : Nat) (expect : Except Snappy.Error ByteArray → Bool) : IO Unit := do
  let (before, after, result) := snapshotAndDecompress input cap
  r.check s!"{name} input unchanged" (before == after)
  r.check name (expect result)

/-- `compress x` then `decompress` with cap `x.size` returns `x`. -/
private def checkRound (r : Runner) (name : String) (input : ByteArray) : IO Unit := do
  match Snappy.compress input with
  | .error _ =>
    r.check s!"{name} round trip compresses" false
  | .ok compressed =>
    checkDecompress r s!"{name} round trip" compressed input.size (succeedsWith input)

/-- Fail when a provenance or record field carries a different string. -/
private def expectStr (file field got expected : String) : IO Unit := do
  unless got == expected do
    throw <| IO.userError s!"{file}: {field} expected {expected}, observed {got}"

/-- The fixture names the Go raw-block tool, module, version, and API. -/
private def checkProvenance (file : String) (j : Json) : IO Unit := do
  let p ← jObj file j "_provenance"
  expectStr file "_provenance.generatedBy" (← jStr file p "generatedBy")
    "packages/codec/snappy/tools/go-fixtures/main.go"
  expectStr file "_provenance.module" (← jStr file p "module") "github.com/golang/snappy"
  expectStr file "_provenance.version" (← jStr file p "version") "v0.0.4"
  expectStr file "_provenance.api" (← jStr file p "api") "Encode/Decode"
  expectStr file "_provenance.format" (← jStr file p "format")
    "raw Snappy block, not framed stream"

/-- Go `Encode` output decompresses to the committed input. -/
private def checkGoCase (r : Runner) (file : String) (c : Json) : IO Unit := do
  let name ← jStr file c "name"
  let input ← unhex s!"{file} {name} inputHex" (← jStr file c "inputHex")
  let compressed ← unhex s!"{file} {name} compressedHex" (← jStr file c "compressedHex")
  checkDecompress r s!"go {name}" compressed input.size (succeedsWith input)

/--
The recorded compressed bytes are a regression of this binding.
`Snappy.compress` still emits them, and `Snappy.decompress` returns the input.
-/
private def checkNativeCase (r : Runner) (file : String) (c : Json) : IO Unit := do
  let name ← jStr file c "name"
  expectStr file s!"nativeEncode {name} record" (← jStr file c "record")
    "native backend regression"
  let input ← unhex s!"{file} {name} inputHex" (← jStr file c "inputHex")
  let compressedHex ← jStr file c "compressedHex"
  let compressed ← unhex s!"{file} {name} compressedHex" compressedHex
  checkExact r s!"native {name}" input compressedHex
  checkDecompress r s!"native {name} decode" compressed input.size (succeedsWith input)

/-- Read `Tests/fixtures/snappy-go-v0.0.4.json` and check both directions. -/
private def checkGoFixture (r : Runner) : IO Unit := do
  let file := "snappy-go-v0.0.4.json"
  let j ← loadFixture file
  checkProvenance file j
  for c in ← jArr file j "goEncode" do
    checkGoCase r file c
  for c in ← jArr file j "nativeEncode" do
    checkNativeCase r file c

/-- The next xorshift64* state. The multiply is not part of this step. -/
private def xorshift64 (s : UInt64) : UInt64 :=
  let s := s ^^^ (s >>> 12)
  let s := s ^^^ (s <<< 25)
  s ^^^ (s >>> 27)

/-- The xorshift64* sample of a state. The state itself stays unchanged. -/
private def sample (s : UInt64) : UInt64 :=
  s * (0x2545F4914F6CDD1D : UInt64)

/-- `n` varied bytes from a fixed seed. Each byte comes from `sample`. -/
private def genBytes (n : Nat) : ByteArray := Id.run do
  let mut state : UInt64 := 0xA5A5A5A5A5A5A5A5
  let mut out : ByteArray := ByteArray.empty
  for _ in [0:n] do
    state := xorshift64 state
    let drawn := sample state
    out := out.push ((drawn >>> 56).toUInt8)
  return out

/--
Lengths around a literal-length boundary and around one block.
`kBlockSize` is 65536. 65535 fits in one block and is one byte short.
65536 is exactly one block. 65537 begins a second block. 131073 is two
blocks plus one byte.
-/
private def generatedLengths : List Nat :=
  [1, 12, 60, 61, 256, 4096, 65535, 65536, 65537, 131073]

/-- Compress, repeat the compression, and decompress at the exact cap. -/
private def checkGenerated (r : Runner) (n : Nat) : IO Unit := do
  let input := genBytes n
  let name := s!"generated {n}"
  let (before, after, result) := snapshotAndCompress input
  r.check s!"{name} input unchanged" (before == after)
  match result with
  | .error _ =>
    r.check s!"{name} compresses" false
  | .ok compressed =>
    let again := Snappy.compress input
    let afterAgain := bytesAfter again input
    r.check s!"{name} input unchanged again" (before == afterAgain)
    match again with
    | .ok repeated =>
      r.check s!"{name} repeat" (compressed == repeated)
    | .error _ =>
      r.check s!"{name} repeat" false
    checkDecompress r s!"{name} round trip" compressed input.size (succeedsWith input)

/--
32 iterations. Each one checks its result. The blocks stay short, so the
loop exercises the extern and the result pair without a long CI run.
The generated lengths cover the block boundary separately.
-/
private def repeatCount : Nat := 32

/-- One thousand public round trips. The runner prints a failing iteration. -/
private def publicTripCount : Nat := 1000

/-- Compress and decompress one small input, and check every result. -/
private def checkPublicTrips (r : Runner) (input : ByteArray) : IO Unit := do
  for i in [0:publicTripCount] do
    let ok :=
      match Snappy.compress input with
      | .ok compressed =>
        match Snappy.decompress compressed input.size with
        | .ok out => out == input
        | .error _ => false
      | .error _ => false
    r.check s!"public round trip {i}" ok

/--
Succeed, reject a malformed block, then succeed again.
The malformed call sits between the two successes.
-/
private def checkRestore (r : Runner) (input : ByteArray) : IO Unit := do
  match Snappy.compress input with
  | .error _ =>
    r.check "restore compresses" false
  | .ok compressed =>
    checkDecompress r "restore success" compressed input.size (succeedsWith input)
  checkDecompress r "restore malformed" (ofNatList [0x01, 0x00]) 1
    (failsWith Snappy.Error.invalidCompressedData)
  match Snappy.compress input with
  | .error _ =>
    r.check "restore compresses again" false
  | .ok compressed =>
    checkDecompress r "restore success again" compressed input.size (succeedsWith input)

/--
`abcd` followed by one distinct byte, eight times.
Each match is four bytes. In pinned Snappy 1.3.1, `EmitCopy` takes the
`len < 12` entry and returns through `EmitCopyAtMost64<true>`.
A pure run shorter than 18 bytes is one literal, so this pattern is
the short-copy input.
-/
private def shortCopyInput : ByteArray :=
  ofNatList <| List.flatten <| (List.range 8).map fun i =>
    [0x61, 0x62, 0x63, 0x64, 0x41 + i]

/--
Repetitive lengths around `EmitCopy` in pinned Snappy 1.3.1
(`snappy.cc`). A one-byte run keeps the first byte as a literal and
copies the rest.
66 bytes leave a copy of 65. That length is above 64 and below 68, so
the long form emits a 60-byte copy and a remainder below 12.
69 bytes leave a copy of 68. `while (len >= 68)` emits one 64-byte
copy. The generated lengths `60` and `61` already cover the
literal-length encoding change. These checks are round trips.
-/
private def checkCopyBoundaries (r : Runner) : IO Unit := do
  checkRound r "copy below 12" shortCopyInput
  checkRound r "copy above 64" (ofNatList (List.replicate 66 0x61))
  checkRound r "copy at least 68" (ofNatList (List.replicate 69 0x61))

/-- Repeat a successful round trip, a malformed block, and a small cap. -/
private def checkRepeats (r : Runner) (hello : ByteArray) (helloBlock : ByteArray) : IO Unit := do
  let bad := ofNatList [0x01, 0x00]
  for i in [0:repeatCount] do
    let (before, after, result) := snapshotAndCompress hello
    r.check s!"repeat compress {i} input unchanged" (before == after)
    match result with
    | .error _ =>
      r.check s!"repeat compress {i}" false
    | .ok compressed =>
      checkDecompress r s!"repeat decompress {i}" compressed hello.size (succeedsWith hello)
    checkDecompress r s!"repeat malformed {i}" bad 1
      (failsWith Snappy.Error.invalidCompressedData)
    checkDecompress r s!"repeat over cap {i}" helloBlock (hello.size - 1)
      (failsWith Snappy.Error.outputTooLarge)

/-- Phase 3A compression, Phase 3B bounds, Phase 4A hostile blocks, and Phase 4B coverage. -/
def Snappy.run (r : Runner) : IO Unit := do
  r.section "snappy" "google/snappy 1.3.1 raw block (native/check/core.cpp)"
  let hello := ofString "hello hello hello hello"
  let oneByte := ofNatList [0x42]
  let repetitive := ofNatList (List.replicate 16 0x61)
  let binary := ofNatList [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10]
  checkExact r "empty" ByteArray.empty "00"
  checkExact r "hello hello hello hello" hello "171468656c6c6f20420600"
  checkNonempty r "one byte" oneByte
  checkNonempty r "repetitive" repetitive
  checkNonempty r "binary" binary
  match ← parsedHex r "empty block" "00" with
  | none => pure ()
  | some emptyBlock =>
    checkDecompress r "empty block cap 0" emptyBlock 0 (succeedsWith ByteArray.empty)
  match ← parsedHex r "hello block" "171468656c6c6f20420600" with
  | none => pure ()
  | some helloBlock =>
    checkDecompress r "hello exact cap" helloBlock hello.size (succeedsWith hello)
    -- The block declares 23 output bytes. The cap is one byte smaller.
    checkDecompress r "hello declared above cap" helloBlock (hello.size - 1)
      (failsWith Snappy.Error.outputTooLarge)
    -- The same block declares 23 output bytes. Cap 0 is below that length.
    checkDecompress r "hello cap 0" helloBlock 0
      (failsWith Snappy.Error.outputTooLarge)
    checkDecompress r "hello cap 2^32" helloBlock (2 ^ 32) (succeedsWith hello)
    checkDecompress r "hello cap 2^64" helloBlock (2 ^ 64) (succeedsWith hello)
  -- `0x01` is a one-byte length for one output byte, and no element follows.
  let truncatedPayload := ofNatList [0x01]
  checkDecompress r "empty compressed" ByteArray.empty 0
    (failsWith Snappy.Error.invalidCompressedData)
  checkDecompress r "truncated payload within cap" truncatedPayload 1
    (failsWith Snappy.Error.invalidCompressedData)
  -- The same block advertises one byte. Cap 0 rejects it before the
  -- missing payload is validated.
  checkDecompress r "cap before truncated payload" truncatedPayload 0
    (failsWith Snappy.Error.outputTooLarge)
  -- `ff ff ff ff 0f` is the longest legal length. It stores `2^32 - 1`.
  -- Cap 1024 is below that length, so the call rejects the block before
  -- it allocates the advertised output.
  checkDecompress r "cap before max length" (ofNatList [0xff, 0xff, 0xff, 0xff, 0x0f]) 1024
    (failsWith Snappy.Error.outputTooLarge)
  -- `0x80` sets the length continuation bit and then the block ends.
  checkDecompress r "truncated length header" (ofNatList [0x80]) 1
    (failsWith Snappy.Error.invalidCompressedData)
  -- Five length bytes. The fifth byte is `0x10`, so the value does not
  -- fit in a 32-bit varint. `Parse32WithLimit` rejects a fifth byte
  -- that is not below 16.
  checkDecompress r "overflowing length" (ofNatList [0x80, 0x80, 0x80, 0x80, 0x10]) 1
    (failsWith Snappy.Error.invalidCompressedData)
  -- Length 1, then literal tag `0x00` (one literal byte). The byte is absent.
  checkDecompress r "truncated literal" (ofNatList [0x01, 0x00]) 1
    (failsWith Snappy.Error.invalidCompressedData)
  -- `ff 06 00 00` followed by ASCII `sNaPpY` is the standard Snappy
  -- framed-stream identifier. This call gives those bytes to the
  -- raw-block API. The prefix stores a length below the cap, so the
  -- result comes from the block check.
  checkDecompress r "framed stream identifier"
    (ofNatList [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59])
    1024
    (failsWith Snappy.Error.invalidCompressedData)
  -- Tag `0x02` is the assigned two-byte-offset copy. Its two offset
  -- bytes are absent. The low two bits select that copy form.
  checkDecompress r "truncated copy operands" (ofNatList [0x01, 0x02]) 1
    (failsWith Snappy.Error.invalidCompressedData)
  -- Length 1, then tag `0x02` (copy one byte) and offset 1. No output
  -- byte exists yet, so the offset points before the output.
  checkDecompress r "copy before output" (ofNatList [0x01, 0x02, 0x01, 0x00]) 1
    (failsWith Snappy.Error.invalidCompressedData)
  -- The hello block ends `42 06 00`: copy 17 bytes from offset 6.
  -- The same bytes with offset 0 are not a valid copy.
  let corruptedHello := ofNatList
    [0x17, 0x14, 0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x42, 0x00, 0x00]
  checkDecompress r "corrupted hello offset" corruptedHello hello.size
    (failsWith Snappy.Error.invalidCompressedData)
  -- 4096 equal bytes compress to a shorter block. The exact cap is
  -- that length. Cap 1 is below the length the block advertises.
  let highExpansionInput := ofNatList (List.replicate 4096 0x61)
  match Snappy.compress highExpansionInput with
  | .error _ =>
    r.check "high expansion compresses" false
  | .ok compressed =>
    r.check "high expansion compresses smaller" (compressed.size < highExpansionInput.size)
    checkDecompress r "high expansion exact cap" compressed highExpansionInput.size
      (succeedsWith highExpansionInput)
    checkDecompress r "high expansion small cap" compressed 1
      (failsWith Snappy.Error.outputTooLarge)
  checkRound r "empty" ByteArray.empty
  checkRound r "one byte" oneByte
  checkRound r "hello hello hello hello" hello
  checkRound r "repetitive" repetitive
  checkRound r "binary" binary
  checkGoFixture r
  for n in generatedLengths do
    checkGenerated r n
  match ← parsedHex r "repeat hello block" "171468656c6c6f20420600" with
  | none => pure ()
  | some helloBlock =>
    checkRepeats r hello helloBlock
  checkPublicTrips r oneByte
  checkRestore r oneByte
  checkCopyBoundaries r
  r.check "compression size below 2^32"
    (Snappy.Internal.inputWithinLimit ((2 ^ 32) - 1))
  r.check "compression size at 2^32"
    (Snappy.Internal.inputWithinLimit (2 ^ 32) == false)
  r.check "compression size at 2^64"
    (Snappy.Internal.inputWithinLimit (2 ^ 64) == false)
  r.check "2^64 narrows to zero" ((2 ^ 64).toUInt32 == 0)

end Tests
