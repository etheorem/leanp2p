import Tests.Support
import Bytes
import Snappy

/-!
# Snappy raw blocks (unit W6.2, Phases 3A and 3B)

Compression and bounded decompression against `google/snappy` 1.3.1.
The empty block and `hello hello hello hello` use the bytes pinned by
`native/check/core.cpp`. Each borrowed input is snapshotted as a
`List Nat` before the extern call.
-/

set_option autoImplicit false

namespace Tests

open Bytes

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

/-- Phase 3A compression checks and Phase 3B bounded decompression. -/
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
    checkDecompress r "hello short cap" helloBlock (hello.size - 1)
      (failsWith Snappy.Error.outputTooLarge)
    checkDecompress r "hello cap 2^32" helloBlock (2 ^ 32) (succeedsWith hello)
    checkDecompress r "hello cap 2^64" helloBlock (2 ^ 64) (succeedsWith hello)
  let truncated := ofNatList [0x01]
  checkDecompress r "empty compressed" ByteArray.empty 0
    (failsWith Snappy.Error.invalidCompressedData)
  checkDecompress r "truncated within cap" truncated 1
    (failsWith Snappy.Error.invalidCompressedData)
  checkDecompress r "truncated over cap" truncated 0
    (failsWith Snappy.Error.outputTooLarge)
  checkRound r "empty" ByteArray.empty
  checkRound r "one byte" oneByte
  checkRound r "hello hello hello hello" hello
  checkRound r "repetitive" repetitive
  checkRound r "binary" binary

end Tests
