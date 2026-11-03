# leanp2p snappy: architecture

`codec/snappy` compresses and decompresses one raw Snappy block. Both
operations are deterministic. The bytes are a Lean `ByteArray`. The
package owns that block and the bound on its decompressed size. It
binds pinned `google/snappy` behind the Lean surface below. A later
pure Lean body can replace the native body behind the same surface
(PLAN W6.2; ARCHITECTURE §3.6).

Callers import `Snappy`. They do not import the native helper, and
they do not depend on the native library.

## What this package owns

W6.2 owns these facts:

- Raw Snappy block compression.
- Raw Snappy block decompression.
- The check of the uncompressed length stored in the raw block.
- The caller cap on decompressed output.
- Structured errors for predictable input and limit failures.
- The Lean and native ownership boundary.
- A reproducible build of the pinned `google/snappy` sources.

## Outside this package

These facts belong to other units:

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

## Modules

| Module | Responsibility |
|---|---|
| `Snappy.lean` | Public `Snappy.Error`, `compress`, and `decompress`. The private externs, the cap clamp, the status maps, and the internal-panic extern. |

The public surface and the private adapter are small, so both stay in
the root module. The root `lean_lib` keeps its one-module glob until a
submodule earns the wider glob. The native helper under `native/` has
no public Lean module and no second API.

All public declarations live in the `Snappy` namespace.

## Public surface

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

Phase 3A implements `compress`. Phase 3B implements `decompress`.
`decompress` takes the bytes first and the cap second.

The functions are pure because the block operation is deterministic
(ARCHITECTURE §3.6). The type carries no `IO`. Callers see `Snappy`
and `Except`. They do not see a native status, a pointer, a workspace
size, or a build flag. A later pure Lean body keeps these signatures.

A raw block stores its own uncompressed length. That length is a field
of the block. It is separate from the req/resp framing length that
W6.3 reads before it calls `decompress`.

## Errors

`Snappy.Error` is the package inductive for a predictable input or
limit failure (ARCHITECTURE §3.5). A failure of that kind is an
`Except` value. It is never an `IO.userError`.

**`inputTooLarge`.** The compression input is at least `2^32` bytes
long, or the shim cannot calculate a safe native output allocation.
The Lean wrapper rejects the length before calling native code.
The shim checks it again before narrowing the length, calculating the
maximum compressed size, or allocating the compressed output.

**`invalidCompressedData`.** The bytes are not one valid raw block.
The case covers a bad or truncated length, a truncated payload,
truncated copy operands, a bad copy offset, a malformed literal or
copy encoding, a decoded length that disagrees with the block, and
any other failed check of the raw block. A cap rejection
uses `outputTooLarge` instead.

**`outputTooLarge`.** The block's advertised uncompressed length is
above `maxOutputSize`. The native shim validates the advertised length
and compares it with the clamped cap before allocating the decompressed
output.

`maxOutputSize` is a `Nat` on the public function. The private adapter
clamps a cap of `2^32` or greater to `UInt32.max`. A cap of that
size accepts every uncompressed length the raw format can store.

Runtime allocation exhaustion is not a `Snappy.Error`. A pure binding
has no `IO.Error` channel for it. The call follows ARCHITECTURE §3.6:
the Lean runtime allocator does not return, and a failed native scratch
allocation calls `lean_internal_panic_out_of_memory`.

## Native boundary

The raw externs are private. Their logical shape is:

```lean
@[extern "leanp2p_snappy_compress"]
private opaque compressRaw
  (src : @& ByteArray) :
  UInt32 × ByteArray

@[extern "leanp2p_snappy_decompress"]
private opaque decompressRaw
  (src : @& ByteArray)
  (maxOutputSize : UInt32) :
  UInt32 × ByteArray
```

Lean 4.34 may require a small change to that spelling. The public
signatures stay as written above. The symbols keep the `leanp2p_`
prefix.

The native status is the first field of the pair. The four numeric
codes are the shared private ABI vocabulary:

| Code | Meaning |
|---|---|
| `0` | success |
| `1` | input too large |
| `2` | invalid compressed data |
| `3` | output too large |

The public `Error` hides the numbers. Compression accepts ordinary
codes `0` and `1` only. Code `0` is a nonempty raw block. Code `1` is
`.inputTooLarge`. Codes `2` and `3` are decompression outcomes.

Compression treats codes `2` and `3`, an empty success, a reported
length past the allocated capacity, and every unknown code as internal
invariant failures. The call is `leanp2p_snappy_internal_panic`. It
calls `lean_internal_panic` and ends the process. The reason argument
uses a separate category:

| Category | Meaning |
|---|---|
| `0` | successful compression produced an empty output |
| `1` | compression returned an unexpected status |
| `2` | the reported compressed length exceeded the allocated capacity |
| `3` | a block that passed validation then failed `RawUncompress` |
| `4` | decompression returned an unexpected status |

Statuses `2`, `3`, and every unknown compression status select
category `1`. The wrapper returns the helper call from each impossible
branch. Empty input compresses to the one-byte block `0x00`. A
successful compression result is nonempty.

Decompression accepts ordinary codes `0`, `2`, and `3`. Code `0` is
the decompressed block, and that block may be empty. Code `2` is
`.invalidCompressedData`. Code `3` is `.outputTooLarge`. Code `1` is a
compression outcome. Decompression treats code `1` and every unknown
code as category `4`.

The caller cap is a `Nat`. `clampOutputCap` compares it with `2^32`
before `Nat.toUInt32`. A cap of `2^32` or more becomes `0xFFFFFFFF`
and accepts every length the raw format can store.

The shim parses the advertised length, compares that length with the
clamped cap, and validates the whole block before it allocates. A cap
rejection therefore precedes a payload-malformation rejection. An
allocation that cannot represent an accepted length calls
`lean_internal_panic`. It does not return a `Snappy.Error`.

Every ordinary return from the shim is a valid Lean object. An error
status carries an owned empty array. The wrapper reads a successful
decompression only from status `0`.

## Ownership

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
the required alignment before it builds the context. The context object
and the workspace are separate storage.

A failed scratch allocation calls `lean_internal_panic_out_of_memory`.
A Lean-owned result uses the Lean runtime allocator. Exhaustion of
either allocation does not return. It is not an empty success, and it
is not a `Snappy.Error`.

## Upstream pin and source layout

The pin is `google/snappy` release `1.3.1`, commit
`9c28114a38866f6deeaa826db918293bc28ae410`, from
`https://github.com/google/snappy`. The license is the upstream BSD
text. One copy of that text is the canonical license.

The imported upstream files are `COPYING` and these seven sources:

- `snappy.cc`
- `snappy.h`
- `snappy-internal.h`
- `snappy-sinksource.cc`
- `snappy-sinksource.h`
- `snappy-stubs-internal.h`
- `snappy-stubs-public.h.in`

The import review checks this list, and the bytes of each file, against
that commit. The block build may omit `snappy-stubs-internal.cc`. That
omission stands when those objects link and the audit of every object
and of the archive finds no missing required symbol.

```text
packages/codec/snappy/
├── Snappy.lean
├── docs/
│   ├── ARCHITECTURE.md
│   └── PLAN.md
├── upstream/
│   ├── COPYING
│   ├── UPSTREAM.toml
│   ├── SHA256SUMS
│   └── pristine/
│       └── <seven upstream source/header files>
├── patches/
│   └── 0001-block-only.patch
├── scripts/
│   └── audit-native.py
└── native/
    ├── lakefile.lean
    ├── check/
    │   ├── core.cpp
    │   ├── abort.cpp
    │   └── internal-panic.cpp
    ├── include/
    │   ├── config.h
    │   └── snappy-stubs-public.h
    ├── vendor/
    │   └── snappy/
    │       └── <committed patched sources compiled by Lake>
    └── shim.cpp
```

A Lake requirement may rename a build-support file. The roles stay.
`upstream/COPYING` is the canonical license. `upstream/pristine/` holds
the seven source files. `UPSTREAM.toml` records the repository, the
release, the commit, and the imported file list. `SHA256SUMS` has one
SHA-256 line for `COPYING` and one line for every pristine source file.
`patches/0001-block-only.patch` is the readable record of every change.
`native/vendor/snappy/` is the patched source tree the ordinary build
compiles. It does not carry a second copy of the license. The patch
verifier copies only `upstream/pristine/`, applies the patch, and
compares that reconstructed tree with `native/vendor/snappy/`.
`native/include/config.h` and `native/include/snappy-stubs-public.h`
are build-support files. They are not upstream sources. The
build-support headers make platform-feature choices explicit. The
pristine control and the patched define-disabled build use matched
configuration, and every production configuration remains subject to
the platform and interoperability tests below.

The ordinary `lake build` reads the committed patched tree. It does
not apply the patch, and it does not use the network. The verifier
uses `git apply`. This package does not carry a Lean parser for a
unified diff.

## Offline patch verification

The offline verifier does seven steps:

1. It checks every hash in `SHA256SUMS`, including `COPYING`.
2. It copies only `upstream/pristine/` into a fresh temporary directory.
3. It applies `patches/0001-block-only.patch` with `git apply`.
4. It fails when the patch does not apply cleanly.
5. It compares that directory, byte for byte, with
   `native/vendor/snappy/`.
6. It fails on a changed file, a missing file, or an extra file.
7. It uses no network.

A passing run shows that the pin, the pristine snapshot, the patch,
and the compiled tree agree. It does not show that the tree matches
the Snappy specification. The import review is the separate check that
the pristine bytes and the hashes match the pinned commit.

## The block-only patch

Every behavioral change to the upstream sources sits inside
`LEANP2P_SNAPPY_BLOCK_ONLY`.

The patch may drop unused `std::string`, public `Source`/`Sink`,
iovec, and other APIs outside the selected raw-buffer block path.
`ByteArraySource` and `UncheckedByteArraySink` stay in the production
compile, because the raw-buffer functions use them. The patch may
allocate the compression workspace with an explicit native allocator.
It may add the class-specific `operator delete` functions that keep a
live C++ runtime reference out of the production objects.

The patched sources, built without the define, keep the selected
upstream behavior on the raw-block cases. A class-specific `operator
delete` aborts if it is called. A fallback virtual body aborts if it
is called. Both are guarded by the define. The whole change is one
patch, so a reviewer can read it in one pass.

The production shim has no test counter and no mutable test state.
Malformed input comes back as `invalidCompressedData`. The shim does
not aim malformed input at an upstream assertion. An upstream assertion
that marks an impossible internal state stays a process-level native
fault. It does not become a public input error.

A review of the guards is regression evidence together with the
three builds below. It is not a proof that the patched library matches
upstream on every input.

## Native build

The root `lakefile.toml` cannot express this native archive. The leaf
therefore keeps one small helper at `native/`, required by path
(ARCHITECTURE §2; PRINCIPLES §4.2). The root file stays
`lakefile.toml`. The helper is versioned with this repository. It adds
no public Lean API and no second version boundary. Its `lakefile.lean`
is a `.lean` file under `packages/codec`, so the import lint applies
to it: the file does not contain the token `libp2p`.

The helper builds the static archive. It also exposes the package-local
command that runs the native boundary check. That command must build or
fetch the archive and link the check against that same archive. A
disposable Lake experiment showed that a namespaced script can run a
native program and return its exit code. That experiment did not link
the production archive.

The ordinary build is offline. The native compile uses `-Wall`,
`-Wextra`, and `-Werror`. It disables C++ exceptions and RTTI. It
enables function and data sections so the linker can drop an unused
upstream path.

Upstream `snappy.cc` adds one flag after `-Werror`:
`-Wno-ignored-attributes`. GCC 15 diagnoses ignored alignment
attributes on the upstream `std::pair<__m128i, __m128i>` construct.
The diagnostic is suppressed only while compiling upstream `snappy.cc`.
Every other warning remains an error. `snappy-sinksource.cc`,
`shim.cpp`, and the check drivers keep full `-Werror`. The upstream
source and the SIMD behavior remain unchanged. This narrow suppression
satisfies the repository warning-free build requirement. The pinned
source stays unpatched.

The audit reads every object, and it reads the archive. None of them
may carry a live unresolved reference to a `std::` runtime facility,
a global `operator new`, a global `operator delete`, `__cxa_*`, or
`__gxx_personality*`. A C++ runtime that Lean already links does not
excuse one of those references in a Snappy object or in the archive.
Checked `malloc`, `free`, `memcpy`, and a non-returning `abort` stay
available where this document names them.

## Three builds

The three builds share the compiler, the language mode, the
optimization level, the public-header substitutions, a compatible
`config.h`, and the raw-block corpus.

**Pristine control.** Compile the unmodified pristine sources. Run the
selected raw-block cases.

**Patched, define disabled.** Compile `native/vendor/snappy/` without
`LEANP2P_SNAPPY_BLOCK_ONLY`. Run the same cases. The compression bytes,
the decompression results, and the relevant public symbol surface match
the pristine control. This comparison is regression evidence.

**Patched, define enabled.** Compile the same patched tree with
`LEANP2P_SNAPPY_BLOCK_ONLY`. Run the production block tests. Audit
every object and the archive for the forbidden C++ runtime references
above.

## Phase 2C commands

The ordinary `lake build` does not run these commands. The root Snappy
library waits only for `snappyNative/snappy`.

`lake build snappyNative/snappyBoundary` builds the three archives and
links one boundary driver to each archive. It checks that the three
raw-block transcripts match. It shows that the production link uses
the production archive. It does not show that a guarded body aborts,
and it does not show that a forbidden C++ runtime symbol is absent.

`lake build snappyNative/snappyAbort` compiles `native/check/abort.cpp`
once and links that object to `libsnappy.a` once. Twelve child
processes call the four fallback bodies and the eight class-specific
`operator delete` functions. Each child must exit 86 from its
`SIGABRT` handler. This shows those direct calls abort. It does not
show that a later shim avoids the calls.

`lake build snappyNative/snappyAudit` reads `snappy.block.o`,
`snappy-sinksource.block.o`, `shim.o`, and `libsnappy.a`. It rejects an
unresolved `std::` facility, a global `operator new`, a global
`operator delete`, `__cxa_*`, and `__gxx_personality*`. Lean runtime
symbols stay on a separate exact allowlist and are reported as
`lean-runtime`. `shim.o` defines exactly `leanp2p_snappy_compress`,
`leanp2p_snappy_decompress`, and `leanp2p_snappy_internal_panic`. It
checks the guarded symbols and the three production
archive members. The pristine archive and the define-disabled archive
stay the two upstream objects. It compares the defined global symbols
of the pristine build and the define-disabled build. The local run is
macOS ARM64. The Linux x86-64 audit, ASan, LSan, and the Snappy-free
control passed in the Phase 4C job recorded in the package plan.

`lake build snappyNative/snappyInternalPanic` compiles
`native/check/internal-panic.cpp` and links that object to `libsnappy.a`
once. The child sets `LEAN_ABORT_ON_PANIC` and calls
`leanp2p_snappy_internal_panic`. The parent accepts the SIGABRT
sentinel. Ordinary tests do not set that variable.

`lake build snappyNative/snappyValidation` runs the boundary check, the
abort check, the internal-panic check, and the audit. Those targets
share the production object jobs. The command does not compile a second
`snappy.cc` or `snappy-sinksource.cc`.

## Trust and validation

The trusted computing base is the pinned `google/snappy` sources, the
guarded patch, the native shim, the Lean native ABI and runtime
allocator, the system C runtime, and the C and C++ compiler and linker.
The Lean kernel does not check the native bytes. This package states no
axiom and no theorem that equates the native library with a pure Lean
model.

The evidence is empirical:

- Known raw-block vectors.
- Empty input, one-byte input, text, repetitive bytes, incompressible
  bytes, binary input, a boundary length, and a larger input.
- Generated round trips that the test fixes in advance.
- For each generated `x`, if `compress x = .ok c`, then
  `decompress c x.size = .ok x`. This is a test, not a theorem about
  the extern.
- Fixtures produced by Go Snappy and committed with the tests.
- Malformed input and truncated input.
- Truncated copy operands, an invalid copy offset, and a malformed literal or copy encoding.
- A cap equal to the advertised length, and a cap below it.
- Extreme and overflowing length encodings.
- A repeated run of success and failure.
- A borrowed input that is unchanged after the call.
- The object and archive symbol audit.
- The same audit on Linux x86-64.
- Paired ASan and LSan runs of the Snappy executable and a Snappy-free
  control built the same way.

## A later pure implementation

Callers depend on `Snappy.Error`, `compress`, and `decompress`. A pure
Lean body may replace the native bodies and keep the raw-block
behavior, the three errors, the `2^32` input bound, the output cap, and
the public signatures. No networking caller imports the private adapter
or the helper package.

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
