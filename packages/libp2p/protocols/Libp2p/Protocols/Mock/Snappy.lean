/-!
# Snappy block mock

`Snappy` (root PLAN W6.2, issue #6, PR #35) is not merged. This mock
declares the surface #35 gives `codec/snappy`: the `Error` inductive,
`compress`, and the bounded `decompress`. The surface follows the
protocols package docs, "Decisions": raw block `compress` and
`decompress`, and no framing (RULES.md, "Working ahead of the tree").

The values are pure Lean, so the req/resp suite can read the frames
that go's snappy writes before the binding lands:

* `compress` writes one literal element per call. The result is a valid
  snappy block that never shrinks the input.
* `decompress` reads the whole block format of
  `vendor/snappy/format_description.txt`, literals and the three copy
  kinds, and checks the
  preamble length against the cap before it allocates.

## Integration

Delete this module. Replace each `Mock.Snappy` with `Snappy`, and import
`Snappy` where the mock was imported; that covers the default of
`ReqResp.Compressor` in the writer. The names and the arguments are
the same. The native compressor shrinks repetitive data, so the frame
writer's choice between a compressed and an uncompressed chunk starts
to pick compressed chunks; the suite checks both kinds already.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Snappy

/-- Why a raw block call failed, the arms of #35. -/
inductive Error where
  /-- The compression input is 2^32 bytes or longer. -/
  | inputTooLarge
  /-- The bytes are not one valid raw snappy block. -/
  | invalidCompressedData
  /-- The preamble length exceeds the caller's cap. -/
  | outputTooLarge
  deriving Repr, DecidableEq

/-- The little-endian base-128 varint of the preamble, section 1. -/
def preamble (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut v := n
  -- Five groups carry the 2^32 - 1 maximum; the loop stops early.
  for _ in [0:5] do
    if v < 0x80 then
      return out.push v.toUInt8
    out := out.push (v % 0x80 + 0x80).toUInt8
    v := v / 0x80
  return out

/-- The tag and length bytes of one literal element, section 2.1. -/
def literalHeader (len : Nat) : ByteArray :=
  let m := len - 1
  if m < 60 then ByteArray.mk #[(m * 4).toUInt8]
  else if m < 2 ^ 8 then ByteArray.mk #[(60 * 4).toUInt8, m.toUInt8]
  else if m < 2 ^ 16 then
    ByteArray.mk #[(61 * 4).toUInt8, m.toUInt8, (m / 2 ^ 8).toUInt8]
  else if m < 2 ^ 24 then
    ByteArray.mk #[(62 * 4).toUInt8, m.toUInt8, (m / 2 ^ 8).toUInt8, (m / 2 ^ 16).toUInt8]
  else
    ByteArray.mk #[(63 * 4).toUInt8, m.toUInt8, (m / 2 ^ 8).toUInt8,
      (m / 2 ^ 16).toUInt8, (m / 2 ^ 24).toUInt8]

/-- Compress `src` as one raw block: the preamble, then one literal. -/
opaque compress (src : ByteArray) : Except Error ByteArray :=
  if 2 ^ 32 ≤ src.size then .error .inputTooLarge
  else if src.size = 0 then .ok (preamble 0)
  else .ok (preamble src.size ++ literalHeader src.size ++ src)

/-- Read the preamble: the length and the offset after it. A sixth
group, or a value at 2^32 or above, is no snappy block. -/
def readPreamble (src : ByteArray) : Except Error (Nat × Nat) := Id.run do
  let mut v := 0
  for i in [0:5] do
    let some b := src[i]? | return .error .invalidCompressedData
    v := v + (b.toNat % 0x80) * 0x80 ^ i
    if b.toNat < 0x80 then
      return if v < 2 ^ 32 then .ok (v, i + 1) else .error .invalidCompressedData
  return .error .invalidCompressedData

/-- The little-endian value of `k` bytes at `pos`, or `none` past the end. -/
def readLE (src : ByteArray) (pos k : Nat) : Option Nat := Id.run do
  let mut v := 0
  for i in [0:k] do
    let some b := src[pos + i]? | return none
    v := v + b.toNat * 256 ^ i
  return some v

/-- Append `len` bytes that start `offset` bytes back. A copy longer than
its offset repeats the bytes it has just written (section 2.2). -/
def copyBack (out : ByteArray) (offset len : Nat) : ByteArray := Id.run do
  let mut o := out
  let start := out.size - offset
  for i in [0:len] do
    o := o.push (o.get! (start + i))
  return o

/-- One element at `pos`: the output after it and the next offset. -/
def element (src out : ByteArray) (pos : Nat) : Except Error (ByteArray × Nat) := do
  let some tag := src[pos]? | throw .invalidCompressedData
  let t := tag.toNat
  let kind := t % 4
  if kind = 0 then
    -- A literal: the length is in the tag up to 60, else in 1 to 4 bytes.
    let m := t / 4
    let (len, body) ←
      if m < 60 then pure (m + 1, pos + 1)
      else match readLE src (pos + 1) (m - 59) with
        | some v => pure (v + 1, pos + 1 + (m - 59))
        | none => throw .invalidCompressedData
    if src.size < body + len then throw .invalidCompressedData
    pure (out ++ src.extract body (body + len), body + len)
  else
    let (len, offset, next) ←
      if kind = 1 then
        match readLE src (pos + 1) 1 with
        | some lo => pure (4 + (t / 4) % 8, (t / 32) * 256 + lo, pos + 2)
        | none => throw .invalidCompressedData
      else
        let k := if kind = 2 then 2 else 4
        match readLE src (pos + 1) k with
        | some off => pure (t / 4 + 1, off, pos + 1 + k)
        | none => throw .invalidCompressedData
    -- Offset zero and an offset past the output are illegal, section 2.2.
    if offset = 0 ∨ out.size < offset then throw .invalidCompressedData
    pure (copyBack out offset len, next)

/-- Decompress one raw block, with at most `maxOutputSize` bytes out.
The preamble length is checked against the cap before any element is
read. Every element consumes at least one byte, so `src.size` rounds
bound the loop. -/
opaque decompress (src : ByteArray) (maxOutputSize : Nat) : Except Error ByteArray := do
  let (len, start) ← readPreamble src
  if maxOutputSize < len then throw .outputTooLarge
  let mut out := ByteArray.empty
  let mut pos := start
  for _ in [0:src.size] do
    if src.size ≤ pos ∨ len < out.size then break
    let (o, p) ← element src out pos
    out := o
    pos := p
  if pos = src.size ∧ out.size = len then pure out
  else throw .invalidCompressedData

end Libp2p.Protocols.Mock.Snappy
