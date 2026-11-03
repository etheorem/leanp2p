#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>

#include "snappy-sinksource.h"

// Abort-path driver for the production archive.
// Each process installs a SIGABRT handler, then calls one guarded
// function. The handler exits with status 86. A function that returns
// makes this process exit with status 2.
//
// The calls are direct. Each delete check selects one overload with a
// function pointer and passes a null deallocation argument. A null
// pointer is a permitted argument to a deallocation function. These
// calls do not evaluate a delete expression.

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

static int returned(const char* mode) {
  fprintf(stderr, "The mode %s returned from the guarded call.\n", mode);
  return 2;
}

static int runMode(const char* mode) {
  if (strcmp(mode, "sink-append") == 0) {
    snappy::Sink sink;
    char byte = 'x';
    sink.Append(&byte, 1);
    return returned(mode);
  }
  if (strcmp(mode, "source-available") == 0) {
    snappy::Source source;
    (void)source.Available();
    return returned(mode);
  }
  if (strcmp(mode, "source-peek") == 0) {
    snappy::Source source;
    size_t length = 1;
    (void)source.Peek(&length);
    return returned(mode);
  }
  if (strcmp(mode, "source-skip") == 0) {
    snappy::Source source;
    source.Skip(0);
    return returned(mode);
  }
  if (strcmp(mode, "sink-delete") == 0) {
    void (*fn)(void*) noexcept =
        static_cast<void (*)(void*) noexcept>(&snappy::Sink::operator delete);
    fn(nullptr);
    return returned(mode);
  }
  if (strcmp(mode, "sink-delete-sized") == 0) {
    void (*fn)(void*, size_t) noexcept =
        static_cast<void (*)(void*, size_t) noexcept>(&snappy::Sink::operator delete);
    fn(nullptr, 0);
    return returned(mode);
  }
  if (strcmp(mode, "source-delete") == 0) {
    void (*fn)(void*) noexcept =
        static_cast<void (*)(void*) noexcept>(&snappy::Source::operator delete);
    fn(nullptr);
    return returned(mode);
  }
  if (strcmp(mode, "source-delete-sized") == 0) {
    void (*fn)(void*, size_t) noexcept =
        static_cast<void (*)(void*, size_t) noexcept>(&snappy::Source::operator delete);
    fn(nullptr, 0);
    return returned(mode);
  }
  if (strcmp(mode, "byte-array-source-delete") == 0) {
    void (*fn)(void*) noexcept =
        static_cast<void (*)(void*) noexcept>(&snappy::ByteArraySource::operator delete);
    fn(nullptr);
    return returned(mode);
  }
  if (strcmp(mode, "byte-array-source-delete-sized") == 0) {
    void (*fn)(void*, size_t) noexcept = static_cast<void (*)(void*, size_t) noexcept>(
        &snappy::ByteArraySource::operator delete);
    fn(nullptr, 0);
    return returned(mode);
  }
  if (strcmp(mode, "unchecked-byte-array-sink-delete") == 0) {
    void (*fn)(void*) noexcept = static_cast<void (*)(void*) noexcept>(
        &snappy::UncheckedByteArraySink::operator delete);
    fn(nullptr);
    return returned(mode);
  }
  if (strcmp(mode, "unchecked-byte-array-sink-delete-sized") == 0) {
    void (*fn)(void*, size_t) noexcept = static_cast<void (*)(void*, size_t) noexcept>(
        &snappy::UncheckedByteArraySink::operator delete);
    fn(nullptr, 0);
    return returned(mode);
  }
  fprintf(stderr, "The mode %s is unknown.\n", mode);
  return 2;
}

int main(int argc, char** argv) {
  if (argc != 2) {
    fprintf(stderr, "The abort driver expects one mode.\n");
    return 2;
  }
  if (disableCore() != 0 || installAbortHandler() != 0) {
    fprintf(stderr, "The abort driver could not install its SIGABRT handler.\n");
    return 2;
  }
  return runMode(argv[1]);
}
