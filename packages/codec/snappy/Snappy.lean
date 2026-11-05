/-!
# Snappy

Raw Snappy block compression and bounded decompression for unit W6.2.
Both public functions operate on one raw block. Production code in this
module imports neither `Bytes` nor a native header. The native body
lives in `native/shim.cpp`.
-/

set_option autoImplicit false

namespace Snappy

/-- A predictable raw-block input or limit failure. -/
inductive Error where
  /-- The compression input is outside the raw Snappy or safe native allocation bound. -/
  | inputTooLarge
  /-- The bytes are not one valid raw Snappy block. -/
  | invalidCompressedData
  /-- The advertised decompressed length exceeds the caller's bound. -/
  | outputTooLarge
  deriving Repr, DecidableEq

/-!
`leanp2p_snappy_internal_panic` takes a category, calls
`lean_internal_panic`, and ends the process. The categories are
separate from the four shared native status codes.

- `0`: successful compression produced an empty output.
- `1`: compression returned an unexpected status. Statuses `2` and `3`,
  and every unknown compression status, use this category.
- `2`: the reported compressed length exceeded the allocated capacity.
- `3`: a block that passed validation then failed `RawUncompress`.
- `4`: decompression returned an unexpected status. Status `1` and every
  unknown decompression status use this category.
-/

/-- Category for a successful compression that produced an empty output. -/
private def emptyOutputReason : UInt32 := 0

/-- Category for a compression status outside `0` and `1`. -/
private def unexpectedStatusReason : UInt32 := 1

/-- Category for a decompression status outside `0`, `2`, and `3`. -/
private def unexpectedDecompressReason : UInt32 := 4

/--
Compress one borrowed block.
Status `0` carries the raw block. Status `1` carries an empty array
and means the input or the output bound is outside the safe range.
-/
@[extern "leanp2p_snappy_compress"]
private opaque compressRaw (src : @& ByteArray) : UInt32 × ByteArray

/-- End the process for an internal compression invariant failure. -/
@[never_extract, extern "leanp2p_snappy_internal_panic"]
private opaque internalPanic (reason : UInt32) : Except Error ByteArray

/-- Map a compression status onto `Except Error`. -/
private def fromCompress (code : UInt32) (out : ByteArray) : Except Error ByteArray :=
  match code with
  | 0 =>
    if out.isEmpty then
      internalPanic emptyOutputReason
    else
      .ok out
  | 1 => .error .inputTooLarge
  | _ => internalPanic unexpectedStatusReason

namespace Internal

/--
Decide whether a raw-block input length may be compressed.
`compress` calls this predicate before `compressRaw`.
A length below `2^32` is accepted. `2^32` and every larger length
are rejected. The comparison reads the `Nat` and allocates nothing.
The native shim repeats the check on `size_t` before it narrows the
length. `compress` returns before a rejected array reaches that check,
so the shim comparison is reviewed in `shim.cpp` and has no test hook.
Callers use `compress`.
-/
def inputWithinLimit (n : Nat) : Bool :=
  n < 2 ^ 32

end Internal

/-- Compress bytes as one raw Snappy block. -/
def compress (src : ByteArray) : Except Error ByteArray :=
  if Internal.inputWithinLimit src.size then
    let (code, out) := compressRaw src
    fromCompress code out
  else
    .error .inputTooLarge

/--
Decompress one borrowed block.
`maxOutputSize` is already clamped. Status `0` carries the output,
including an empty block. Status `2` means the block is invalid.
Status `3` means the advertised length exceeds the cap.
-/
@[extern "leanp2p_snappy_decompress"]
private opaque decompressRaw (src : @& ByteArray) (maxOutputSize : UInt32) : UInt32 × ByteArray

/--
Clamp a caller cap to the raw-format maximum.
A cap of `2^32` or more accepts every length the format can store.
The comparison runs before `Nat.toUInt32`.
-/
private def clampOutputCap (n : Nat) : UInt32 :=
  if n ≥ 2 ^ 32 then
    0xFFFFFFFF
  else
    n.toUInt32

/-- Map a decompression status onto `Except Error`. -/
private def fromDecompress (code : UInt32) (out : ByteArray) : Except Error ByteArray :=
  match code with
  | 0 => .ok out
  | 2 => .error .invalidCompressedData
  | 3 => .error .outputTooLarge
  | _ => internalPanic unexpectedDecompressReason

/--
Decompress one raw Snappy block, rejecting an advertised output length
above `maxOutputSize`.
-/
def decompress (src : ByteArray) (maxOutputSize : Nat) : Except Error ByteArray :=
  let (code, out) := decompressRaw src (clampOutputCap maxOutputSize)
  fromDecompress code out

end Snappy
