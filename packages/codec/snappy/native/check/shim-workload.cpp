#include <lean/lean.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

// Workload for the production shim ABI.
//
// The process calls `leanp2p_snappy_compress` and
// `leanp2p_snappy_decompress`. It does not call the upstream C++
// entry points itself. The Lean runtime is the real one linked by
// `leanc`: this file initializes that runtime, builds scalar arrays
// with `lean_alloc_sarray`, and shuts the runtime down.
//
// `lean::finalize_runtime_module` is the shutdown exported by the
// runtime. The public `lean.h` does not declare it.

extern "C" void lean_initialize_runtime_module(void);

namespace lean {
void finalize_runtime_module();
}

extern "C" lean_object* leanp2p_snappy_compress(b_lean_obj_arg src);
extern "C" lean_object* leanp2p_snappy_decompress(b_lean_obj_arg src,
                                                  uint32_t maxOutputSize);

namespace {

constexpr uint32_t kStatusOk = 0;
constexpr uint32_t kStatusInvalid = 2;
constexpr uint32_t kStatusOutputTooLarge = 3;
constexpr int kRepeats = 8;
constexpr size_t kRepetitive = 4096;
constexpr size_t kMultiBlock = 65537;

const char kHello[] = "hello hello hello hello";
const uint8_t kBinary[] = {0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10};
const uint8_t kMalformed[] = {0x01, 0x00};

int failf(const char* message) {
  std::fprintf(stderr, "snappy shim workload: %s\n", message);
  return 1;
}

lean_object* makeBytes(const uint8_t* data, size_t size) {
  lean_object* bytes = lean_alloc_sarray(1, size, size);
  if (size != 0) {
    std::memcpy(lean_sarray_cptr(bytes), data, size);
  }
  return bytes;
}

uint32_t statusOf(lean_object* pair) {
  return lean_unbox_uint32(lean_ctor_get(pair, 0));
}

lean_object* payloadOf(lean_object* pair) {
  return lean_ctor_get(pair, 1);
}

bool sameBytes(lean_object* bytes, const uint8_t* data, size_t size) {
  if (lean_sarray_size(bytes) != size) {
    return false;
  }
  if (size == 0) {
    return true;
  }
  return std::memcmp(lean_sarray_cptr(bytes), data, size) == 0;
}

int roundTrip(const char* name, const uint8_t* data, size_t size) {
  lean_object* input = makeBytes(data, size);
  lean_object* compressed = leanp2p_snappy_compress(input);
  if (!sameBytes(input, data, size)) {
    lean_dec(compressed);
    lean_dec(input);
    std::fprintf(stderr, "snappy shim workload: %s changed the input\n", name);
    return 1;
  }
  if (statusOf(compressed) != kStatusOk) {
    lean_dec(compressed);
    lean_dec(input);
    std::fprintf(stderr, "snappy shim workload: %s compression failed\n", name);
    return 1;
  }
  lean_object* compressedBytes = payloadOf(compressed);
  lean_inc(compressedBytes);
  lean_object* restored = leanp2p_snappy_decompress(
      compressedBytes, static_cast<uint32_t>(size));
  lean_dec(compressedBytes);
  bool ok = statusOf(restored) == kStatusOk &&
            sameBytes(payloadOf(restored), data, size) &&
            sameBytes(input, data, size);
  lean_dec(restored);
  lean_dec(compressed);
  lean_dec(input);
  if (!ok) {
    std::fprintf(stderr, "snappy shim workload: %s round trip failed\n", name);
    return 1;
  }
  return 0;
}

int expectDecompress(const char* name, lean_object* compressed, uint32_t cap,
                     uint32_t expected) {
  lean_object* result = leanp2p_snappy_decompress(compressed, cap);
  uint32_t status = statusOf(result);
  lean_dec(result);
  if (status != expected) {
    std::fprintf(stderr, "snappy shim workload: %s status %u\n", name, status);
    return 1;
  }
  return 0;
}

int onePass() {
  if (roundTrip("empty", nullptr, 0) != 0) {
    return 1;
  }
  if (roundTrip("text", reinterpret_cast<const uint8_t*>(kHello),
                sizeof kHello - 1) != 0) {
    return 1;
  }
  if (roundTrip("binary", kBinary, sizeof kBinary) != 0) {
    return 1;
  }
  uint8_t* repetitive = static_cast<uint8_t*>(std::malloc(kRepetitive));
  if (repetitive == nullptr) {
    return failf("repetitive allocation failed");
  }
  std::memset(repetitive, 0x61, kRepetitive);
  int repetitiveStatus = roundTrip("repetitive", repetitive, kRepetitive);
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
  int multiStatus = roundTrip("multi-block", multi, kMultiBlock);
  std::free(multi);
  if (multiStatus != 0) {
    return 1;
  }

  lean_object* malformed = makeBytes(kMalformed, sizeof kMalformed);
  int malformedStatus =
      expectDecompress("malformed", malformed, 1, kStatusInvalid);
  lean_dec(malformed);
  if (malformedStatus != 0) {
    return 1;
  }

  lean_object* hello = makeBytes(reinterpret_cast<const uint8_t*>(kHello),
                                 sizeof kHello - 1);
  lean_object* helloBlock = leanp2p_snappy_compress(hello);
  if (statusOf(helloBlock) != kStatusOk) {
    lean_dec(helloBlock);
    lean_dec(hello);
    return failf("hello compression failed");
  }
  lean_object* helloBytes = payloadOf(helloBlock);
  lean_inc(helloBytes);
  int capStatus = expectDecompress(
      "over cap", helloBytes, static_cast<uint32_t>(sizeof kHello - 2),
      kStatusOutputTooLarge);
  lean_dec(helloBytes);
  lean_dec(helloBlock);
  lean_dec(hello);
  return capStatus;
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
