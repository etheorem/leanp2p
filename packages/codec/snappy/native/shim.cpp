#include <lean/lean.h>

#include <cstddef>
#include <cstdint>
#include <cstdlib>

#include "snappy.h"

// Compression shim for one raw Snappy block.
//
// The borrowed input is `b_lean_obj_arg`. This file does not increment,
// decrement, consume, mutate, or retain that object.
//
// Ordinary compression statuses:
//   0  a nonempty raw block
//   1  the input or the output bound is outside the safe range
//
// `leanp2p_snappy_internal_panic` categories, separate from those statuses:
//   0  successful compression produced an empty output
//   1  compression returned an unexpected status
//   2  the reported compressed length exceeded the allocated capacity
// Statuses 2 and 3, and every unknown status, use category 1 on the Lean side.

namespace {

constexpr uint32_t kStatusOk = 0;
constexpr uint32_t kStatusInputTooLarge = 1;
constexpr uint32_t kReasonEmptyOutput = 0;
constexpr uint32_t kReasonOverCapacity = 2;
constexpr size_t kSizeMax = ~static_cast<size_t>(0);

lean_object* makeResult(uint32_t code, lean_object* bytes) {
  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint32(code));
  lean_ctor_set(pair, 1, bytes);
  return pair;
}

lean_object* rejectInput() {
  return makeResult(kStatusInputTooLarge, lean_alloc_sarray(1, 0, 0));
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
    default:
      break;
  }
  lean_internal_panic(message);
}

extern "C" LEAN_EXPORT lean_object*
leanp2p_snappy_compress(b_lean_obj_arg src) {
  const size_t inputSize = lean_sarray_size(src);
  if (inputSize > static_cast<size_t>(UINT32_MAX)) {
    return rejectInput();
  }

  const size_t bound = snappy::MaxCompressedLength(inputSize);
  if (bound == 0 || bound == kSizeMax ||
      lean_alloc_sarray_would_overflow(1, bound)) {
    return rejectInput();
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
