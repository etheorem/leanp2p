#include <cstddef>
#include <cstdlib>

// Disposable LeakSanitizer probe.
// The allocation is intentionally left allocated. This file is not
// linked into the Snappy archive or the ordinary tests.

namespace {

__attribute__((noinline)) void leakOnce(size_t size) {
  void* block = std::malloc(size);
  __asm__ __volatile__("" : : "r"(block) : "memory");
}

}  // namespace

int main() {
  leakOnce(64);
  return 0;
}
