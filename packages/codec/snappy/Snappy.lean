/-!
# Snappy

Raw Snappy block compression for unit W6.2. The public function
compresses one `ByteArray` into one raw block. Production code in this
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
  and every unknown status, use this category.
- `2`: the reported compressed length exceeded the allocated capacity.
-/

/-- Category for a successful compression that produced an empty output. -/
private def emptyOutputReason : UInt32 := 0

/-- Category for a compression status outside `0` and `1`. -/
private def unexpectedStatusReason : UInt32 := 1

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

/-- Compress bytes as one raw Snappy block. -/
def compress (src : ByteArray) : Except Error ByteArray :=
  if src.size ≥ 2 ^ 32 then
    .error .inputTooLarge
  else
    let (code, out) := compressRaw src
    fromCompress code out

end Snappy
