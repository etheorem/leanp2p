#include <lean/lean.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

// Matched runtime and linker control for the shim workload.
//
// The process initializes and finalizes the same Lean runtime as
// `shim-workload.cpp`. It builds scalar arrays at the same input sizes
// and runs the same number of passes. It links through `leanc` and the
// same sanitizer flags when the hardening script builds that pair.
// It contains no Snappy symbol and no Snappy archive. The arrays it
// checks are Lean scalar arrays at those sizes.

extern "C" void lean_initialize_runtime_module(void);

namespace lean {
void finalize_runtime_module();
}

namespace {

constexpr int kRepeats = 8;
constexpr size_t kRepetitive = 4096;
constexpr size_t kMultiBlock = 65537;

const char kHello[] = "hello hello hello hello";
const uint8_t kBinary[] = {0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10};

int failf(const char* message) {
  std::fprintf(stderr, "snappy runtime control: %s\n", message);
  return 1;
}

int checkArray(const char* name, const uint8_t* data, size_t size) {
  lean_object* bytes = lean_alloc_sarray(1, size, size);
  if (size != 0) {
    std::memcpy(lean_sarray_cptr(bytes), data, size);
  }
  bool ok = lean_sarray_size(bytes) == size &&
            (size == 0 ||
             std::memcmp(lean_sarray_cptr(bytes), data, size) == 0);
  lean_dec(bytes);
  if (!ok) {
    std::fprintf(stderr, "snappy runtime control: %s bytes differ\n", name);
    return 1;
  }
  return 0;
}

int onePass() {
  if (checkArray("empty", nullptr, 0) != 0) {
    return 1;
  }
  if (checkArray("text", reinterpret_cast<const uint8_t*>(kHello),
                 sizeof kHello - 1) != 0) {
    return 1;
  }
  if (checkArray("binary", kBinary, sizeof kBinary) != 0) {
    return 1;
  }
  uint8_t* repetitive = static_cast<uint8_t*>(std::malloc(kRepetitive));
  if (repetitive == nullptr) {
    return failf("repetitive allocation failed");
  }
  std::memset(repetitive, 0x61, kRepetitive);
  int repetitiveStatus = checkArray("repetitive", repetitive, kRepetitive);
  std::free(repetitive);
  if (repetitiveStatus != 0) {
    return 1;
  }
  uint8_t* multi = static_cast<uint8_t*>(std::malloc(kMultiBlock));
  if (multi == nullptr) {
    return failf("multi-block allocation failed");
  }
  for (size_t i = 0; i < kMultiBlock; ++i) {
    multi[i] = static_cast<uint8_t>(i * 17 + 3);
  }
  int multiStatus = checkArray("multi-block", multi, kMultiBlock);
  std::free(multi);
  return multiStatus;
}

}  // namespace

int main() {
  lean_initialize_runtime_module();
  int status = 0;
  for (int i = 0; i < kRepeats; ++i) {
    status = onePass();
    if (status != 0) {
      break;
    }
  }
  lean::finalize_runtime_module();
  return status;
}
