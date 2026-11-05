#include <lean/lean.h>

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>

// Child for `leanp2p_snappy_internal_panic`.
// The parent links this object with the production archive. The helper
// reference extracts `shim.o` from that archive. This declaration stays
// an ordinary return so the compiler keeps the CONTINUED path. The
// production definition in `shim.cpp` remains no-return. Setup disables
// core files, sets `LEAN_ABORT_ON_PANIC`, and then installs the SIGABRT
// handler. A return prints CONTINUED and exits 2.

extern "C" lean_object* leanp2p_snappy_internal_panic(uint32_t reason);

static const int kSentinel = 86;

static void onAbort(int signo) {
  (void)signo;
  _exit(kSentinel);
}

static int installAbortHandler(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = onAbort;
  if (sigemptyset(&action.sa_mask) != 0) {
    return 2;
  }
  if (sigaction(SIGABRT, &action, 0) != 0) {
    return 2;
  }
  return 0;
}

static int disableCore(void) {
  struct rlimit limit;
  limit.rlim_cur = 0;
  limit.rlim_max = 0;
  if (setrlimit(RLIMIT_CORE, &limit) != 0) {
    return 2;
  }
  return 0;
}

int main(void) {
  if (disableCore() != 0) {
    return 2;
  }
  if (setenv("LEAN_ABORT_ON_PANIC", "1", 1) != 0) {
    return 2;
  }
  if (installAbortHandler() != 0) {
    return 2;
  }
  lean_object* result = leanp2p_snappy_internal_panic(1);
  (void)result;
  fputs("CONTINUED\n", stdout);
  return 2;
}
