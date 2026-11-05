#include <cstddef>
#include <cstdlib>

// Disposable AddressSanitizer probe.
// The read after `free` must be reported. This file is not linked into
// the Snappy archive or the ordinary tests.

namespace {

__attribute__((noinline)) char useAfterFree() {
  char* block = static_cast<char*>(std::malloc(8));
  if (block == nullptr) {
    return 0;
  }
  block[0] = 1;
  std::free(block);
  return block[0];
}

}  // namespace

int main() {
  char value = useAfterFree();
  return value == 1 ? 0 : 2;
}
