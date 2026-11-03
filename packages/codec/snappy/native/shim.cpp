#include <lean/lean.h>

#include <cstddef>
#include <cstdint>
#include <cstdlib>

#include "snappy.h"

// Shim for one raw Snappy block.
//
// The borrowed input is `b_lean_obj_arg`. This file does not increment,
// decrement, consume, mutate, or retain that object.
//
// Ordinary statuses, shared by compression and decompression:
//   0  success
//   1  the compression input or output bound is outside the safe range
//   2  the compressed bytes are not one valid raw block
//   3  the advertised length exceeds the caller cap
//
// `leanp2p_snappy_internal_panic` categories, separate from those statuses:
//   0  successful compression produced an empty output
//   1  compression returned an unexpected status
//   2  the reported compressed length exceeded the allocated capacity
//   3  a block that passed validation then failed RawUncompress
//   4  decompression returned an unexpected status
// Compression statuses 2 and 3, and every unknown compression status,
// use category 1 on the Lean side. Decompression status 1 and every
// unknown decompression status use category 4.

namespace {

constexpr uint32_t kStatusOk = 0;
constexpr uint32_t kStatusInputTooLarge = 1;
constexpr uint32_t kStatusInvalid = 2;
constexpr uint32_t kStatusOutputTooLarge = 3;
constexpr uint32_t kReasonEmptyOutput = 0;
constexpr uint32_t kReasonOverCapacity = 2;
constexpr uint32_t kReasonValidatedUncompress = 3;
constexpr size_t kSizeMax = ~static_cast<size_t>(0);

lean_object* makeResult(uint32_t code, lean_object* bytes) {
  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint32(code));
  lean_ctor_set(pair, 1, bytes);
  return pair;
}

lean_object* emptyResult(uint32_t code) {
  return makeResult(code, lean_alloc_sarray(1, 0, 0));
}

}  // namespace

extern "C" LEAN_EXPORT LEAN_NORETURN lean_object*
leanp2p_snappy_internal_panic(uint32_t reason) {
  const char* message = "snappy: unknown internal failure";
  switch (reason) {
    case 0:
      message = "snappy: successful compression produced an empty output";
      break;
    case 1:
      message = "snappy: compression returned an unexpected status";
      break;
    case 2:
      message = "snappy: reported compressed length exceeded allocated capacity";
      break;
    case 3:
      message = "snappy: validated block failed RawUncompress";
      break;
    case 4:
      message = "snappy: decompression returned an unexpected status";
      break;
    default:
      break;
  }
  lean_internal_panic(message);
}

extern "C" LEAN_EXPORT lean_object*
leanp2p_snappy_compress(b_lean_obj_arg src) {
  const size_t inputSize = lean_sarray_size(src);
  // `Snappy.Internal.inputWithinLimit` rejects this length before the
  // extern call. The comparison here remains for a direct native caller.
  // It tests the `size_t` length and does not narrow that length first.
  if (inputSize > static_cast<size_t>(UINT32_MAX)) {
    return emptyResult(kStatusInputTooLarge);
  }

  const size_t bound = snappy::MaxCompressedLength(inputSize);
  if (bound == 0 || bound == kSizeMax ||
      lean_alloc_sarray_would_overflow(1, bound)) {
    return emptyResult(kStatusInputTooLarge);
  }

  const size_t workspaceBytes = snappy::CompressionContext::WorkspaceSize();
  if (workspaceBytes == 0) {
    lean_internal_panic("snappy: compression workspace size is zero");
  }
  void* workspace = std::malloc(workspaceBytes);
  if (workspace == nullptr) {
    lean_internal_panic_out_of_memory();
  }
  const auto address = reinterpret_cast<uintptr_t>(workspace);
  if (address % alignof(std::max_align_t) != 0) {
    std::free(workspace);
    lean_internal_panic("snappy: compression workspace is not aligned");
  }

  lean_object* bytes = lean_alloc_sarray(1, 0, bound);
  static const char kLiveByte = 0;
  const char* input = inputSize == 0
      ? &kLiveByte
      : reinterpret_cast<const char*>(lean_sarray_cptr(src));
  char* output = reinterpret_cast<char*>(lean_sarray_cptr(bytes));
  size_t written = 0;
  {
    snappy::CompressionContext context(workspace, workspaceBytes);
    snappy::RawCompress(input, inputSize, output, &written,
                        snappy::CompressionOptions(), &context);
  }
  std::free(workspace);

  if (written == 0) {
    return leanp2p_snappy_internal_panic(kReasonEmptyOutput);
  }
  if (written > bound) {
    return leanp2p_snappy_internal_panic(kReasonOverCapacity);
  }
  lean_sarray_set_size(bytes, written);
  return makeResult(kStatusOk, bytes);
}

extern "C" LEAN_EXPORT lean_object*
leanp2p_snappy_decompress(b_lean_obj_arg src, uint32_t maxOutputSize) {
  const size_t inputSize = lean_sarray_size(src);
  static const char kLiveByte = 0;
  const char* input = inputSize == 0
      ? &kLiveByte
      : reinterpret_cast<const char*>(lean_sarray_cptr(src));

  size_t advertised = 0;
  if (!snappy::GetUncompressedLength(input, inputSize, &advertised)) {
    return emptyResult(kStatusInvalid);
  }
  if (advertised > static_cast<size_t>(maxOutputSize)) {
    return emptyResult(kStatusOutputTooLarge);
  }
  if (!snappy::IsValidCompressedBuffer(input, inputSize)) {
    return emptyResult(kStatusInvalid);
  }
  if (advertised > static_cast<size_t>(UINT32_MAX) ||
      lean_alloc_sarray_would_overflow(1, advertised)) {
    lean_internal_panic("snappy: decompressed length is not a safe allocation size");
  }

  lean_object* bytes = lean_alloc_sarray(1, advertised, advertised);
  static char kLiveOutput = 0;
  char* output = advertised == 0
      ? &kLiveOutput
      : reinterpret_cast<char*>(lean_sarray_cptr(bytes));
  if (!snappy::RawUncompress(input, inputSize, output)) {
    return leanp2p_snappy_internal_panic(kReasonValidatedUncompress);
  }
  return makeResult(kStatusOk, bytes);
}
