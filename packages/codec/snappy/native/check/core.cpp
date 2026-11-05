#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "snappy.h"

// Raw-block boundary driver.
// The caller supplies the transcript path. The process writes that file
// itself. A failed check returns a nonzero status and writes the reason
// to stderr. The transcript has no addresses, times, or paths.
//
// The compression workspace comes from malloc. The context is destroyed
// before that workspace is released. Empty input uses a live dummy byte
// so the call does not pass a null pointer.

static const size_t kRepeatLength = 8192;
static const size_t kRandomLength = 4096;
static const uint32_t kRandomSeed = 0xC0FFEE01u;
static const char kHello[] = "hello hello hello hello";
static const char kHelloHex[] = "171468656c6c6f20420600";
static const char kEmptyHex[] = "00";
static const char kHex[] = "0123456789abcdef";

static_assert(snappy::kBlockSize == 65536,
              "The length cases use the Snappy block size 65536.");

enum CaseKind {
  kEmpty,
  kOneByte,
  kHelloCase,
  kRepetitive,
  kBinary,
  kRandom,
  kLen65535,
  kLen65536,
  kLen65537,
  kMultiBlock
};

struct CaseSpec {
  const char* name;
  CaseKind kind;
  const char* expect_hex;
};

struct CaseResult {
  const char* name;
  size_t input_length;
  size_t advertised_length;
  size_t compressed_length;
  unsigned char* compressed;
};

static const CaseSpec kCases[] = {
  {"empty", kEmpty, kEmptyHex},
  {"one-byte", kOneByte, NULL},
  {"hello", kHelloCase, kHelloHex},
  {"repetitive", kRepetitive, NULL},
  {"binary", kBinary, NULL},
  {"pseudo-random", kRandom, NULL},
  {"len-65535", kLen65535, NULL},
  {"len-65536", kLen65536, NULL},
  {"len-65537", kLen65537, NULL},
  {"multi-block", kMultiBlock, NULL},
};

static const size_t kCaseCount = sizeof kCases / sizeof kCases[0];

static int failf(const char* fmt, ...) {
  fprintf(stderr, "snappy boundary: ");
  va_list args;
  va_start(args, fmt);
  vfprintf(stderr, fmt, args);
  va_end(args);
  fputc('\n', stderr);
  return 1;
}

static size_t input_capacity() {
  size_t multi = snappy::kBlockSize * 2 + 1;
  size_t cap = kRepeatLength;
  if (kRandomLength > cap) cap = kRandomLength;
  if (multi > cap) cap = multi;
  return cap;
}

static void fill_index_bytes(unsigned char* dst, size_t n) {
  for (size_t i = 0; i < n; i++) {
    dst[i] = (unsigned char)(i & 0xffu);
  }
}

// xorshift32. The seed and the shift counts are fixed.
static void fill_random(unsigned char* dst, size_t n) {
  uint32_t x = kRandomSeed;
  for (size_t i = 0; i < n; i++) {
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    dst[i] = (unsigned char)(x & 0xffu);
  }
}

static int fill_input(CaseKind kind, unsigned char* dst, size_t cap, size_t* len) {
  size_t n = 0;
  switch (kind) {
    case kEmpty:
      n = 0;
      break;
    case kOneByte:
      n = 1;
      if (n > cap) return failf("the one-byte input does not fit");
      dst[0] = 0x42;
      break;
    case kHelloCase:
      n = sizeof kHello - 1;
      if (n > cap) return failf("the hello input does not fit");
      memcpy(dst, kHello, n);
      break;
    case kRepetitive:
      n = kRepeatLength;
      if (n > cap) return failf("the repetitive input does not fit");
      memset(dst, 0x61, n);
      break;
    case kBinary: {
      static const unsigned char kBytes[] = {
        0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10
      };
      n = sizeof kBytes;
      if (n > cap) return failf("the binary input does not fit");
      memcpy(dst, kBytes, n);
      break;
    }
    case kRandom:
      n = kRandomLength;
      if (n > cap) return failf("the pseudo-random input does not fit");
      fill_random(dst, n);
      break;
    case kLen65535:
      n = snappy::kBlockSize - 1;
      if (n > cap) return failf("the 65535-byte input does not fit");
      fill_index_bytes(dst, n);
      break;
    case kLen65536:
      n = snappy::kBlockSize;
      if (n > cap) return failf("the 65536-byte input does not fit");
      fill_index_bytes(dst, n);
      break;
    case kLen65537:
      n = snappy::kBlockSize + 1;
      if (n > cap) return failf("the 65537-byte input does not fit");
      fill_index_bytes(dst, n);
      break;
    case kMultiBlock:
      n = snappy::kBlockSize * 2 + 1;
      if (n > cap) return failf("the multi-block input does not fit");
      fill_index_bytes(dst, n);
      break;
  }
  if (n > 0xffffffffu) return failf("%s", "an input length does not fit in 32 bits");
  *len = n;
  return 0;
}

static int hex_is(const unsigned char* bytes, size_t n, const char* expect) {
  size_t i = 0;
  for (; expect[i] != '\0'; i++) {
    if ((i / 2) >= n) return 0;
    unsigned char b = bytes[i / 2];
    char got = (i % 2 == 0) ? kHex[b >> 4] : kHex[b & 0x0f];
    if (got != expect[i]) return 0;
  }
  return i == n * 2;
}

static int write_hex(FILE* out, const unsigned char* bytes, size_t n) {
  for (size_t i = 0; i < n; i++) {
    unsigned char b = bytes[i];
    if (fputc(kHex[b >> 4], out) == EOF) return 1;
    if (fputc(kHex[b & 0x0f], out) == EOF) return 1;
  }
  return 0;
}

static int check_case(snappy::CompressionContext* ctx, const CaseSpec* spec,
                      unsigned char* input, size_t cap, CaseResult* out) {
  size_t len = 0;
  if (fill_input(spec->kind, input, cap, &len) != 0) return 1;
  static const unsigned char kDummy = 0;
  const char* src = len == 0 ? (const char*)&kDummy : (const char*)input;
  size_t bound = snappy::MaxCompressedLength(len);
  if (bound == 0) {
    return failf("%s: MaxCompressedLength returned 0", spec->name);
  }
  unsigned char* first = (unsigned char*)malloc(bound);
  unsigned char* second = (unsigned char*)malloc(bound);
  if (first == NULL || second == NULL) {
    free(first);
    free(second);
    return failf("%s: allocation failed", spec->name);
  }
  snappy::CompressionOptions options;
  size_t first_len = 0;
  size_t second_len = 0;
  snappy::RawCompress(src, len, (char*)first, &first_len, options, ctx);
  if (first_len == 0 || first_len > bound) {
    free(first);
    free(second);
    return failf("%s: compressed length %zu is outside the bound %zu",
                 spec->name, first_len, bound);
  }
  snappy::RawCompress(src, len, (char*)second, &second_len, options, ctx);
  if (second_len != first_len || memcmp(first, second, first_len) != 0) {
    free(first);
    free(second);
    return failf("%s: repeated compression differs", spec->name);
  }
  size_t advertised = 0;
  if (!snappy::GetUncompressedLength((const char*)first, first_len, &advertised) ||
      advertised != len) {
    free(first);
    free(second);
    return failf("%s: advertised length %zu differs from input length %zu",
                 spec->name, advertised, len);
  }
  if (!snappy::IsValidCompressedBuffer((const char*)first, first_len)) {
    free(first);
    free(second);
    return failf("%s: IsValidCompressedBuffer failed", spec->name);
  }
  unsigned char dummy_out = 0;
  unsigned char* plain = NULL;
  unsigned char* dest = &dummy_out;
  if (advertised != 0) {
    plain = (unsigned char*)malloc(advertised);
    if (plain == NULL) {
      free(first);
      free(second);
      return failf("%s: allocation failed", spec->name);
    }
    dest = plain;
  }
  if (!snappy::RawUncompress((const char*)first, first_len, (char*)dest)) {
    free(plain);
    free(first);
    free(second);
    return failf("%s: RawUncompress failed", spec->name);
  }
  if (advertised != 0 && memcmp(dest, input, advertised) != 0) {
    free(plain);
    free(first);
    free(second);
    return failf("%s: decompressed bytes differ from the input", spec->name);
  }
  if (spec->expect_hex != NULL && !hex_is(first, first_len, spec->expect_hex)) {
    free(plain);
    free(first);
    free(second);
    return failf("%s: compressed bytes differ from the raw-block vector", spec->name);
  }
  unsigned char* kept = (unsigned char*)malloc(first_len);
  if (kept == NULL) {
    free(plain);
    free(first);
    free(second);
    return failf("%s: allocation failed", spec->name);
  }
  memcpy(kept, first, first_len);
  free(plain);
  free(first);
  free(second);
  out->name = spec->name;
  out->input_length = len;
  out->advertised_length = advertised;
  out->compressed_length = first_len;
  out->compressed = kept;
  return 0;
}

static int write_transcript(const char* path, const CaseResult* results, size_t count) {
  FILE* out = fopen(path, "wb");
  if (out == NULL) return failf("cannot write the transcript");
  for (size_t i = 0; i < count; i++) {
    const CaseResult* r = &results[i];
    if (fprintf(out,
                "case %s\ninput_length %zu\nadvertised_length %zu\n"
                "compressed_length %zu\nvalid yes\nround_trip yes\nrepeat yes\n"
                "compressed ",
                r->name, r->input_length, r->advertised_length,
                r->compressed_length) < 0) {
      fclose(out);
      remove(path);
      return failf("cannot write the transcript");
    }
    if (write_hex(out, r->compressed, r->compressed_length) != 0 ||
        fputc('\n', out) == EOF || fputc('\n', out) == EOF) {
      fclose(out);
      remove(path);
      return failf("cannot write the transcript");
    }
  }
  if (fclose(out) != 0) {
    remove(path);
    return failf("cannot write the transcript");
  }
  return 0;
}

static int run_cases(void* workspace, size_t workspace_size, const char* path) {
  snappy::CompressionContext ctx(workspace, workspace_size);
  size_t cap = input_capacity();
  unsigned char* input = (unsigned char*)malloc(cap == 0 ? 1 : cap);
  if (input == NULL) return failf("allocation failed");
  CaseResult results[sizeof kCases / sizeof kCases[0]];
  memset(results, 0, sizeof results);
  int rc = 1;
  for (size_t i = 0; i < kCaseCount; i++) {
    if (check_case(&ctx, &kCases[i], input, cap, &results[i]) != 0) goto done;
  }
  rc = write_transcript(path, results, kCaseCount);
done:
  for (size_t i = 0; i < kCaseCount; i++) free(results[i].compressed);
  free(input);
  return rc;
}

int main(int argc, char** argv) {
  if (argc != 2 || argv[1] == NULL || argv[1][0] == '\0') {
    return failf("expected one output path");
  }
  size_t workspace_size = snappy::CompressionContext::WorkspaceSize();
  if (workspace_size == 0) {
    return failf("the compression workspace size is 0");
  }
  void* workspace = malloc(workspace_size);
  if (workspace == NULL) return failf("allocation failed");
  int rc = run_cases(workspace, workspace_size, argv[1]);
  free(workspace);
  return rc;
}
