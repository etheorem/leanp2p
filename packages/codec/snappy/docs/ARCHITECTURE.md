# leanp2p snappy: architecture

`codec/snappy` compresses and decompresses one raw Snappy block. Both
operations are deterministic. The bytes are a Lean `ByteArray`. The
package owns that block and the bound on its decompressed size. It
binds pinned `google/snappy` behind the Lean surface below.

Callers import `Snappy`. They do not import the native helper, and
they do not depend on the native library.

## Package boundary

### Owned responsibilities

W6.2 owns these responsibilities:

- Raw Snappy block compression.
- Raw Snappy block decompression.
- The check of the uncompressed length stored in the raw block.
- The caller cap on decompressed output.
- Structured errors for predictable input and limit failures.
- The Lean and native ownership boundary.
- A reproducible build of the pinned `google/snappy` sources.

### Outside this package

These responsibilities belong to other units:

- SSZ serialization and parsing. SSZ stays on the client side of
  req/resp.
- The outer uncompressed-length varint of Ethereum req/resp. That
  prefix is a protobuf varint in the framing, and `codec/varint` owns
  the varint encoding.
- The Snappy framed stream, its chunks, its stream identifier, and
  its masked CRC32C.
- A socket, a stream, a gossip mesh, or a req/resp state machine.

W6.3 owns req/resp framing. It calls this package for the raw block.
A gossip implementation may call `compress` and `decompress` directly.
This package imports no transport, muxer, security, host, or protocol
module.

## Modules and public surface

`Snappy.lean` holds the public declarations and the private native
adapter. All public declarations live in the `Snappy` namespace. The
native helper under `native/` has no public Lean module and no second
API.

```lean
namespace Snappy

inductive Error where
  | inputTooLarge
  | invalidCompressedData
  | outputTooLarge
  deriving Repr, DecidableEq

/-- Compress bytes as one raw Snappy block. -/
def compress :
  ByteArray →
  Except Error ByteArray

/--
Decompress one raw Snappy block, rejecting an advertised output length
above `maxOutputSize`.
-/
def decompress :
  ByteArray →
  Nat →
  Except Error ByteArray

end Snappy
```

`decompress` takes the bytes first and the cap second. The functions
are pure because the block operation is deterministic
(ARCHITECTURE §3.6). The type carries no `IO`. Callers see `Snappy`
and `Except`. They do not see a native status, a pointer, a workspace
size, or a build flag.

A raw block stores its own uncompressed length. That length is a field
of the block. It is separate from the req/resp framing length that
W6.3 reads before it calls `decompress`.

## Errors and failure semantics

`Snappy.Error` is the package inductive for a predictable input or
limit failure (ARCHITECTURE §3.5). A failure of that kind is an
`Except` value. It is never an `IO.userError`.

**`inputTooLarge`.** The compression input is at least `2^32` bytes
long, or the shim cannot calculate a safe native output allocation.
`compress` calls `Snappy.Internal.inputWithinLimit` and rejects that
length before the extern. Callers use `compress`. The shim repeats the
check on `size_t` before it narrows the length, calculates the maximum
compressed size, or allocates the compressed output.

**`invalidCompressedData`.** The bytes are not one valid raw block.
The case covers a bad or truncated length, a truncated payload,
truncated copy operands, a bad copy offset, a malformed literal or
copy encoding, a decoded length that disagrees with the block, and
any other failed check of the raw block. A cap rejection uses
`outputTooLarge`.

**`outputTooLarge`.** The block's advertised uncompressed length is
above `maxOutputSize`. The shim validates that length and compares it
with the clamped cap before it allocates the decompressed output.

Runtime allocation exhaustion is not a `Snappy.Error`. A pure binding
has no `IO.Error` channel for it. The call follows ARCHITECTURE §3.6:
the Lean runtime allocator does not return, and a failed native scratch
allocation calls `lean_internal_panic_out_of_memory`.

## Native ABI

The raw externs are private. They compile in this shape:

```lean
@[extern "leanp2p_snappy_compress"]
private opaque compressRaw (src : @& ByteArray) : UInt32 × ByteArray

@[extern "leanp2p_snappy_decompress"]
private opaque decompressRaw
  (src : @& ByteArray) (maxOutputSize : UInt32) : UInt32 × ByteArray

@[never_extract, extern "leanp2p_snappy_internal_panic"]
private opaque internalPanic (reason : UInt32) : Except Error ByteArray
```

The symbols keep the `leanp2p_` prefix. The native status is the first
field of the pair. Every ordinary return from the shim is a valid Lean
object. An error status carries an owned empty array. The wrapper reads
a successful decompression only from status `0`.

### Status codes

The four numeric codes are the shared private ABI vocabulary:

| Code | Meaning |
|---|---|
| `0` | success |
| `1` | input too large |
| `2` | invalid compressed data |
| `3` | output too large |

The public `Error` hides the numbers. Compression accepts ordinary
codes `0` and `1`. Code `0` is a nonempty raw block. Code `1` is
`.inputTooLarge`. Codes `2` and `3` are decompression outcomes.

Empty input compresses to the one-byte block `0x00`. The shim panics
when a successful compression writes no bytes, and it panics when the
reported length exceeds the allocated capacity. The wrapper repeats
the empty-success check. Compression statuses `2` and `3`, and every
unknown compression status, are internal invariant failures.

Decompression accepts ordinary codes `0`, `2`, and `3`. Code `0` is
the decompressed block, and that block may be empty. Code `2` is
`.invalidCompressedData`. Code `3` is `.outputTooLarge`. Code `1` is
a compression outcome. Decompression treats code `1` and every unknown
code as an internal invariant failure.

### Internal panic categories

`leanp2p_snappy_internal_panic` calls `lean_internal_panic` and ends
the process. The reason argument uses a separate category:

| Category | Meaning |
|---|---|
| `0` | successful compression produced an empty output |
| `1` | compression returned an unexpected status |
| `2` | the reported compressed length exceeded the allocated capacity |
| `3` | a block that passed validation then failed `RawUncompress` |
| `4` | decompression returned an unexpected status |

Statuses `2`, `3`, and every unknown compression status select
category `1`. Decompression status `1` and every unknown decompression
status select category `4`.

### Decompression ordering

The caller cap is a `Nat`. `clampOutputCap` compares it with `2^32`
before `Nat.toUInt32`. A cap of `2^32` or more becomes `0xFFFFFFFF`
and accepts every length the raw format can store.

The shim parses the advertised length, compares that length with the
clamped cap, and validates the whole block before it allocates. A cap
rejection therefore precedes a payload-malformation rejection. An
allocation that cannot represent an accepted length calls
`lean_internal_panic`. It does not return a `Snappy.Error`.

## Ownership and allocation

| Value | Ownership rule |
|---|---|
| Input `ByteArray` | Borrowed with `@&`. The shim receives it as `b_lean_obj_arg`. The shim does not change it, consume it, increment it, or decrement it. |
| Output `ByteArray` | A new Lean-owned scalar array. The shim returns it to Lean. |
| Compression scratch workspace | A native temporary allocation. The shim frees it on every ordinary path. |
| `CompressionContext` | A separate native object over the caller-provided workspace. The shim runs its destructor before it frees the workspace. |
| Decompression output | A new Lean-owned scalar array. The shim allocates it only after the length parses, the cap accepts it, and the full block validates. |

No native pointer outlives the owner that allocated it. The shim never
writes the borrowed input. Any scratch allocation that was made is
released exactly once on every ordinary success or error path.

The shim asks `CompressionContext::WorkspaceSize()` for the workspace
length. It does not store a size measured on one platform. It checks
the required alignment before it builds the context. A misaligned
workspace is freed, and the call then panics. The context object and
the workspace are separate storage. The caller-provided context sets
`owns_working_memory_` false, so its destructor destroys the working
memory in place and does not free that workspace.

A failed scratch allocation calls `lean_internal_panic_out_of_memory`.
A Lean-owned result uses the Lean runtime allocator. Exhaustion of
either allocation does not return. It is not an empty success, and it
is not a `Snappy.Error`.

## Upstream provenance and guarded patch

The pin is `google/snappy` release `1.3.1`, commit
`9c28114a38866f6deeaa826db918293bc28ae410`, from
`https://github.com/google/snappy`. The license is the upstream BSD
text. `upstream/COPYING` is the one canonical copy.

`UPSTREAM.toml` records the repository, the release, the commit, and
the imported file list. `SHA256SUMS` has one SHA-256 line for
`COPYING` and one line for every pristine source. The seven pristine
sources and headers are:

- `snappy.cc`
- `snappy.h`
- `snappy-internal.h`
- `snappy-sinksource.cc`
- `snappy-sinksource.h`
- `snappy-stubs-internal.h`
- `snappy-stubs-public.h.in`

The block build omits `snappy-stubs-internal.cc`; successful linkage
and the symbol audit validate that omission.

Package paths below are relative to `packages/codec/snappy/`;
`Tests/...` paths are relative to the repository root.

| Path | Architectural role |
|---|---|
| `Snappy.lean` | Public API and private native adapter |
| `upstream/` | Pinned pristine source, metadata, hashes, and canonical license |
| `patches/` | Readable guarded upstream patch |
| `native/` | Native helper, shim, compiled vendor tree, and validation drivers |
| `scripts/` | Provenance, symbol, dependency, and hardening checks |
| `tools/go-fixtures/` | Pinned independent Go fixture generator |
| `docs/` | Stable architecture and completed implementation plan |
| `Tests/Snappy.lean` and fixture data | Public-boundary, hostile-input, property, and interoperability tests |

`native/vendor/snappy/` is the patched tree the ordinary build
compiles. It does not carry a second copy of the license.
`native/include/config.h` and `native/include/snappy-stubs-public.h`
are build-support headers. They are not upstream sources. The ordinary
`lake build` reads the committed patched tree. It does not apply the
patch, and it does not use the network.

`scripts/verify-upstream.py` is the offline verifier. It checks every
hash in `SHA256SUMS`, copies only `upstream/pristine/`, and applies
`patches/0001-block-only.patch` with `git apply`. A patch that does
not apply cleanly fails the run. The reconstructed tree must match
`native/vendor/snappy/` byte for byte. A changed file, a missing file,
or an extra file fails the run. The verifier uses no network. This
package does not carry a Lean parser for a unified diff.

A passing run shows that the pin, the pristine snapshot, the patch,
and the compiled tree agree. It does not show that the tree matches
the Snappy specification. The separate import check is that the
pristine bytes and the hashes match the pinned commit.

Every behavioral change to the upstream sources sits inside
`LEANP2P_SNAPPY_BLOCK_ONLY`. The production compile excludes the
`std::string` compress and uncompress entry points and the sink
allocator. `ByteArraySource` and `UncheckedByteArraySink` stay,
because the raw-buffer functions use them. Owned workspace allocation
uses `malloc` and aborts when `malloc` fails. A class-specific
`operator delete` aborts when it is called. A fallback virtual body
aborts when it is called. Both are guarded by the define. The whole
change is one patch.

The patched sources, built without the define, keep the selected
upstream behavior on the raw-block cases. The production shim has no
test counter and no mutable test state. Malformed input comes back as
`invalidCompressedData`. The shim does not aim malformed input at an
upstream assertion. An upstream assertion that marks an impossible
internal state stays a process-level native fault. It does not become
a public input error.

A review of the guards, together with the three builds below, is
regression evidence. It is not a proof that the patched library
matches upstream on every input.

## Native build and validation

The root `lakefile.toml` cannot express this native archive. The leaf
keeps one small helper at `native/`, required by path
(ARCHITECTURE §2; PRINCIPLES §4.2). The root file stays
`lakefile.toml`. The helper is versioned with this repository. It adds
no public Lean API and no second version boundary.

The helper builds the static archive and the validation targets below.
The ordinary `lake build` does not run those targets. The root Snappy
library waits only for `snappyNative/snappy`.

### Matched builds

The three builds share the compiler, the language mode, the
optimization level, the public-header substitutions, a compatible
`config.h`, and the raw-block corpus. The build-support headers make
the platform-feature choices explicit. The pristine control and the
patched define-disabled build use one matched configuration.

**Pristine control.** Compile the unmodified pristine sources. Run the
selected raw-block cases.

**Patched, define disabled.** Compile `native/vendor/snappy/` without
`LEANP2P_SNAPPY_BLOCK_ONLY`. Run the same cases. The compression bytes,
the decompression results, and the relevant public symbol surface match
the pristine control. This comparison is regression evidence.

**Patched, define enabled.** Compile the same patched tree with
`LEANP2P_SNAPPY_BLOCK_ONLY`. Run the production block tests. Audit
every object and the archive for the forbidden C++ runtime references
below.

### Validation targets

`lake build snappyNative/snappyBoundary` builds the three archives and
links one boundary driver to each archive. It checks that the three
raw-block transcripts match. The production link uses the production
archive. The driver does not compile a second copy of the production
objects. The target does not show that a guarded body aborts, and it
does not show that a forbidden C++ runtime symbol is absent.

`lake build snappyNative/snappyAbort` compiles `native/check/abort.cpp`
once and links that object to `libsnappy.a` once. Twelve child
processes call the four fallback bodies and the eight class-specific
`operator delete` functions. Each child must exit 86 from its
`SIGABRT` handler. This shows those direct calls abort. It does not
show that the production shim avoids the calls.

`lake build snappyNative/snappyInternalPanic` compiles
`native/check/internal-panic.cpp` and links that object to
`libsnappy.a` once. The child sets `LEAN_ABORT_ON_PANIC` and calls
`leanp2p_snappy_internal_panic`. The parent accepts the `SIGABRT`
sentinel. Ordinary tests do not set that variable.

`lake build snappyNative/snappyAudit` reads `snappy.block.o`,
`snappy-sinksource.block.o`, `shim.o`, and `libsnappy.a`. It applies
the symbol policy below. Lean runtime symbols stay on a separate exact
allowlist and are reported as `lean-runtime`. `shim.o` defines exactly
the three extern symbols above. The pristine archive and the
define-disabled archive stay the two upstream objects. The audit
compares their defined global symbols. The same audit runs in the
`snappy-native-hardening` CI job on Linux x86-64. That job also runs
the matched ASan and LSan controls. `PLAN.md` records the platform
results.

`lake build snappyNative/snappyValidation` runs the boundary check, the
abort check, the internal-panic check, and the audit. Those targets
share the production object jobs. The command does not compile a second
`snappy.cc` or `snappy-sinksource.cc`.

### Warning and symbol policy

The native compile uses `-Wall`, `-Wextra`, and `-Werror`. It disables
C++ exceptions and RTTI. It enables function and data sections so the
linker can drop an unused path. Upstream `snappy.cc` adds
`-Wno-ignored-attributes` after `-Werror`. GCC 15 diagnoses ignored
alignment attributes on the upstream `std::pair<__m128i, __m128i>`
construct. The suppression applies only while compiling that file.
Every other warning remains an error. `snappy-sinksource.cc`,
`shim.cpp`, and the check drivers keep full `-Werror`. The pinned
source and the SIMD behavior stay unchanged.

The audit reads every object and the archive. None of them may carry a
live unresolved reference to a `std::` runtime facility, a global
`operator new`, a global `operator delete`, `__cxa_*`, or
`__gxx_personality*`. A C++ runtime that Lean already links does not
excuse one of those references. Checked `malloc`, `free`, `memcpy`,
and a non-returning `abort` stay available where this document names
them.

## Trust boundary and replacement strategy

The trusted computing base is the pinned `google/snappy` sources, the
guarded patch, the native shim, the Lean native ABI and runtime
allocator, the system C runtime, and the C and C++ compiler and linker.
The Lean kernel does not check the native bytes. The package states no
axiom and no theorem that equates the native implementation with a
pure model.

The evidence is empirical. `PLAN.md` holds the full matrix and the
platform results. The evidence classes are:

- Known raw-block vectors.
- Generated executable round trips.
- Malformed and over-limit inputs.
- Independent Go fixtures.
- Borrowed-input checks.
- Native symbol and archive audits.
- Matched Snappy and control ASan and LSan runs.

For each generated `x`, if `compress x = .ok c`, then
`decompress c x.size = .ok x`. That check is an executable test. It
is not a theorem about the extern.

A later pure Lean body may replace the native bodies. It keeps
`Snappy.Error`, `compress`, `decompress`, the raw-block behavior, the
`2^32` input bound, and the output cap. Callers stay independent of
native symbols, helper targets, and the patch layout. No networking
caller imports the private adapter or the helper package.

## Owned contracts

1. **Raw block only.** Framing, SSZ, and CRC32C stay outside this
   package.
2. **The public API is pure.** `compress` and `decompress` return
   `Except Snappy.Error`.
3. **A predictable input or limit failure is a `Snappy.Error`.** It
   is never an `IO.userError`.
4. **The shim checks the cap before the decompressed allocation.**
5. **The input is borrowed and immutable.**
6. **The output is a new Lean-owned array.**
7. **The ordinary build is offline** and compiles the committed patched
   tree of the pinned release.
8. **One guarded patch** holds every upstream behavioral change.
9. **Production objects and the archive have no live C++ runtime
   reference** of the kinds named above.
10. **Validation is empirical.** The package claims no unproved
    equivalence between the native library and a pure model.
11. **The public signatures stay stable** for a later pure body.
