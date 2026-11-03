import Tests.Support
import Bytes
import Snappy

/-!
# Snappy compression (unit W6.2, Phase 3A)

Raw-block compression against `google/snappy` 1.3.1. The expected
blocks for the empty input and for `hello hello hello hello` are the
bytes pinned by `native/check/core.cpp`. Each case materializes an
independent content list before the extern call, then compares that
list with the input after the call.
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

/-- Phase 3A compression checks. -/
def Snappy.run (r : Runner) : IO Unit := do
  r.section "snappy" "google/snappy 1.3.1 raw block (native/check/core.cpp)"
  checkExact r "empty" ByteArray.empty "00"
  checkExact r "hello hello hello hello" (ofString "hello hello hello hello")
    "171468656c6c6f20420600"
  checkNonempty r "one byte" (ofNatList [0x42])
  checkNonempty r "repetitive" (ofNatList (List.replicate 16 0x61))
  checkNonempty r "binary" (ofNatList [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10])

end Tests
