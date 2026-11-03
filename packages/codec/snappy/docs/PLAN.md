# leanp2p snappy: plan

This plan refines root unit W6.2 for `codec/snappy`. The root plan owns
order across packages. The package architecture owns the contracts.
This file records the units, reviewed commit checkpoints, and
validation gates used to implement W6.2. Each checkpoint was reviewed
and validated before the next one began. Units 0 through 4 are
complete. The Phase 4D acceptance record states the final evidence.

## Root unit

W6.2 is P0. Its root dependency is W1.2, `base/bytes`. W1.2 has landed.
The approved public surface uses the prelude `ByteArray` and the
package inductive `Snappy.Error`. Production `Snappy.lean` does not
import `Bytes`. `Tests/Snappy.lean` imports `Bytes` for fixtures and
for the input snapshot. That test import does not add a production
dependency.

W6.3 consumes this package. `compress`, `decompress`, and the
bounded-decompression tests have passed, so W6.3 can start on this
API.

## Units

| Unit | Deliverable | Done when |
|---|---|---|
| 0 | The root native-helper exception, the root pure-FFI allocation rule, the Snappy architecture, and this plan | The four documents are committed and agree. |
| 1 | The pinned pristine `google/snappy` 1.3.1 sources, the canonical BSD license, the metadata and hashes, the guarded block-only patch, the committed patched tree, the offline verifier, the package-local Lake helper, the static archive of the patched upstream core, the three build controls, the native boundary command linked to that core archive, and the local object and archive audit | The ordinary build is offline. The verifier rebuilds the compiled tree exactly. The guarded-source gates and the local native-build gates pass. |
| 2 | `Snappy.Error`, the private compression extern, the compression shim, public `compress`, the input-size checks in Lean and in the shim, empty-input compression, known compression regressions, borrowed-input immutability, repeated deterministic compression, native compression-boundary validation, and the compression panics for an unknown status and an impossible result | The shim, the wrapper, and the durable tests land together. No commit contains an untested compression shim. |
| 3 | The private decompression extern, the cap conversion, the native length check before allocation, public `decompress`, the malformed and output-limit results, the minimal valid, malformed, exact-cap, and over-cap tests, and the first public round trips | The public surface in the architecture exists. The output cap is enforced before allocation. No commit contains an untested decompression shim. |
| 4 | The malformed-input matrix, the generated round trips, the Go fixtures, the repeated-call and ownership stress, the production archive audits, the Linux x86-64 run, the paired sanitizer runs, and the acceptance record | All required definition-of-done gates pass. The Linux x86-64 native-hardening gate passes in CI. Local macOS evidence and the provenance checks remain local evidence. W6.3 can call the documented API. |

## Commit checkpoints

### Phase 2A. Upstream provenance

```text
build(snappy): pin google snappy 1.3.1 sources
```

The commit adds `upstream/COPYING`, `upstream/UPSTREAM.toml`,
`upstream/SHA256SUMS`, and the seven pristine source and header files.
The review checks the repository URL, the release, the commit, the
file list, the license, and the hashes against that upstream commit.
After the import, a normal build needs no network. This commit
integrates no native code.

### Phase 2B. Guarded patched source

```text
build(snappy): add verified block-only source patch
```

The commit adds `patches/0001-block-only.patch`,
`native/vendor/snappy/`, the offline verifier, and the build-support
headers the later comparisons need. The review reads the patch. Every
upstream behavioral change sits under `LEANP2P_SNAPPY_BLOCK_ONLY`. The
source contains aborting class-specific `operator delete` functions and
aborting fallback virtual bodies. The verifier rebuilds the committed
patched tree byte for byte, with no changed, missing, or extra file.
This checkpoint does not compile the three builds.

### Phase 2C. Native archive

```text
build(snappy): integrate the native archive
```

The commit adds the package-local `native/lakefile.lean`, the root path
requirement, the static archive of the patched upstream core, the three
matched builds, and the native boundary command. `lake-manifest.json`
is included only when `lake update` changes it. The archive holds the
patched upstream core objects. The Lean shim is not in it yet. The
command links that exact archive. The driver runs raw upstream block
operations from it. It does not exercise the later Lean shim ABI, and
it does not compile a second copy of those objects. The three builds
are the pristine sources, the patched tree without
`LEANP2P_SNAPPY_BLOCK_ONLY`, and the patched tree with the define. The
pristine control and the define-disabled build are compared on the
raw-block cases. Aborting deletes and fallback bodies are checked where
that check is safe. The local audit of every object and of the archive
passes. `lake build` and the existing tests stay green. The ordinary
build stays offline.

### Phase 3A. Compression

```text
feat(snappy): add raw block compression
```

The commit adds the compression entry point, the private compression
extern, `Snappy.Error`, public `compress`, and the first
`Tests/Snappy.lean` cases, registered from `Tests/Main.lean`. It adds
`shim.o` to the production archive. The pristine archive and the
define-disabled archive stay the two upstream objects. A borrowed
input is unchanged. Empty input produces `0x00`. Known compression
cases pass, and repeated compression of the same input is
deterministic for the pinned backend. A length of at least `2^32` is
rejected in the wrapper and again in the shim, with no unsafe
narrowing. Compression accepts ordinary statuses `0` and `1`. Statuses
`2` and `3`, an empty success, a reported length past the allocated
capacity, and an unknown status call `lean_internal_panic` through
`leanp2p_snappy_internal_panic`. The isolated child links the
production archive and checks that helper. A failed test makes the
process exit nonzero.

### Phase 3B. Bounded decompression

```text
feat(snappy): add bounded raw block decompression
```

The commit adds the decompression entry point to `shim.o`, the private
decompression extern, the private cap clamp, public `decompress`, and
the first bounded tests. The shim parses the advertised length,
compares it with the clamped cap, and validates the whole block before
it allocates. A cap rejection precedes a payload-malformation
rejection. An exact cap succeeds. A smaller cap returns
`.outputTooLarge`. Invalid input returns `.invalidCompressedData`.
Empty decompressed output is a successful status `0`. A cap of `2^32`
or greater accepts every length the raw format can store. The
comparison with `2^32` happens before `Nat.toUInt32`. Decompression
status `1` and every unknown status call `lean_internal_panic` through
category `4`. The first public round trips pass: if `compress x = .ok c`,
then `decompress c x.size = .ok x`. The audit requires the three shim
exports. That commit left the hostile input matrix for Phase 4A.

### Phase 4A. Invalid input

```text
test(snappy): cover malformed blocks and limits
```

The suite adds a truncated length header, an overlong or overflowing
length, a truncated payload, truncated copy operands, an invalid copy
offset, a malformed literal or copy encoding, a corrupted block, a
declared output above the cap, an extreme expansion ratio, and the
case where the advertised length exceeds the cap before the payload
is fully validated.

### Phase 4B. Interoperability and stress

```text
test(snappy): add interoperability and stress coverage
```

The suite adds committed raw-block fixtures, the larger deterministic
generated round-trip suite, repeated successful calls, repeated invalid
calls, a check that a borrowed input is unchanged, and larger inputs
around the block boundaries.

### Phase 4C. Linux native hardening

```text
ci(snappy): audit native symbols and sanitizers
```

The job asserts Linux `x86_64`. It audits undefined symbols in every
object and in the archive. It compares the dynamic libraries of the
Snappy executable with a Snappy-free control from the same job. It runs
ASan and LSan on the Snappy executable and on the control. Both leak
runs must exit 0 with no leak report. A leak in either executable
fails the job. The control checks the same runtime and linker. The job
links no second C++ runtime. The job first passed for
`fb0e84cedf0be26561fa14a350aa374e5ef68804`. The acceptance record
cites the later warning-free run.

### Phase 4D. Acceptance record

```text
docs(snappy): record completed validation
```

This commit records the completed validation. The architecture stays as
written, with one status sentence for the completed Linux x86-64 job.

Units 0 through 4 are complete once this acceptance record is
committed. The public API is `Snappy.compress`,
`Snappy.decompress`, and `Snappy.Error`. The constructors are
`inputTooLarge`, `invalidCompressedData`, and `outputTooLarge`.
`Snappy.compress` takes a `ByteArray` and returns
`Except Snappy.Error ByteArray`. `Snappy.decompress` takes a
`ByteArray` and a `Nat` cap and returns `Except Snappy.Error ByteArray`.
`Snappy.Internal.inputWithinLimit` is an unsupported implementation
detail. Callers use `compress`.

The upstream pin is `https://github.com/google/snappy`, release
`1.3.1`, commit `9c28114a38866f6deeaa826db918293bc28ae410`. The Go
fixture tool is the module `leanp2p/snappy-go-fixtures`. It requires
`github.com/golang/snappy` v0.0.4. The module has no replace directive.

The local host is macOS ARM64. Lean is 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, target
`arm64-apple-darwin24.6.0`. `lake build` passed. Both `lake test` runs
reported 9208 passed, 0 failed, 0 todo, and two skips. The skips are
the parked-task check and the borrowed-argument soak. Both need
`/proc/self/status`. The native validation passed. The production
archive members are `snappy.block.o`, `snappy-sinksource.block.o`, and
`shim.o`. The shim exports are `leanp2p_snappy_compress`,
`leanp2p_snappy_decompress`, and `leanp2p_snappy_internal_panic`. The
archive is static. The linked check executables load the system C++
runtime and `libSystem`. The Linux hardening script stops because
`uname -s` is Darwin. That line is the platform guard.

The Linux x86-64 evidence is
[CI run 41706761667](https://github.com/etheorem/leanp2p/actions/runs/41706761667)
for `b5f6876b8b6490f402b39a7a763c8c391c3681d7`. The result is success.
`build-and-test` passed, and `snappy-native-hardening` passed. The
co-author guard and the license acceptance guard also passed for that
commit. The runner is Linux `x86_64`. GCC is 15.2.0. The native
compilation completed with no compiler warnings. Upstream
`snappy.cc` is compiled with `-Wno-ignored-attributes` after `-Werror`.
The package architecture explains that suppression. Lean is 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, target
`x86_64-unknown-linux-gnu`. Both `lake test` runs reported 9211
passed, 0 failed, 0 todo, and 0 skipped. The archive members are the
same three objects. The symbol audit passed. The unsanitized Snappy
and control dynamic libraries match, and both dynamic C++ runtime sets
are empty. The sanitized library sets match, and both link `libasan`.
The Snappy ASan run is clean, and the control ASan run is clean. The
Snappy LSan run is clean, and the control LSan run is clean. The
deliberate use after free is reported as `heap-use-after-free`. The
deliberate leak is reported by LeakSanitizer. The job ends with
`linux-hardening: passed`.

`b5f6876b8b6490f402b39a7a763c8c391c3681d7` is the clean implementation
HEAD. `lake update` and the full acceptance commands ran on the earlier
implementation HEAD
`fb0e84cedf0be26561fa14a350aa374e5ef68804` and passed. `lake update`
exited successfully and left both manifests unchanged. Those commands
were `lake build`, both `lake test` runs,
`scripts/lint-imports.sh`, `git diff --check`,
`python3 packages/codec/snappy/scripts/verify-upstream.py`,
`lake build snappyNative/snappyBoundary`,
`lake build snappyNative/snappyAbort`,
`lake build snappyNative/snappyInternalPanic`,
`lake build snappyNative/snappyAudit`,
`lake build snappyNative/snappyValidation`,
`scripts/vendor-pull.sh --verify`, and
`python3 scripts/extract-vectors.py`. `Tests/vectors` stayed empty in
`git status`. Two generations of the committed Go fixture matched each
other and `Tests/fixtures/snappy-go-v0.0.4.json`.

After this documentation-only Phase 4D diff, `lake build`, both
`lake test` runs, the import lint, and the whitespace check were
repeated successfully.

Linux ARM64 is a best-effort, non-gating portability check. The
official Lean 4.34.0 archive reports `aarch64-unknown-linux-gnu` and
the same commit. `uname` reported Linux and `aarch64`. The upstream
verifier matched. Snappy native validation passed, with the same
archive members and the same shim exports. Root `lake build` passed.
Root `lake test` did not complete because the unrelated crypto backend
requires `OSSL_SIGNATURE_PARAM_NONCE_TYPE`, absent from the tested
Ubuntu 24.04 OpenSSL 3.0.13 headers. The failure is in
`packages/crypto/backend/c/p2pcrypto.c`. The single-capability test and
the import lint therefore did not run in that ARM64 environment. Linux
ARM64 support is incomplete. The required P0 native-hardening gate
is the successful Linux x86-64 CI job.

The trust boundary stays empirical. The Lean kernel does not check the
native bytes. The package states no axiom and no theorem that equates
the native library with a pure model.

## Hardening

| Requirement | Checkpoint | Evidence |
|---|---|---|
| Aborting class-specific `operator delete`, with no no-op delete | Source in Phase 2B; compiled evidence in Phase 2C | Patch review in 2B. Define-enabled checks where they are safe, and the symbol audit, in 2C |
| Every upstream behavioral change under `LEANP2P_SNAPPY_BLOCK_ONLY` | Guards in Phase 2B; comparison in Phase 2C | The readable patch in 2B. The pristine and patched define-disabled comparison in 2C |
| Panic on an unknown status and on an impossible reported compression length | Phases 3A and 3B | Review of the Lean status map and of the native invariants, plus the ordinary-path tests |
| Deterministic vendor-patch verification | Phase 2B | Offline `git apply` and a byte-for-byte comparison |
| Linux x86-64 audit and a matched sanitizer control | Phase 4C | CI logs from a runner that asserts `x86_64` |

The Phase 2B source checks, the Phase 2C builds, and the Phase 3
evidence are local. The Phase 4C logs are CI-only. The
`build-and-test` job on `ubuntu-latest` runs `lake build`, `lake test`,
the single-capability run, the import lint, and the vector provenance
check. The `snappy-native-hardening` job runs the Snappy symbol audit
and the paired sanitizers. The acceptance record cites the passing run.

## Upstream and build gates

The pin is `https://github.com/google/snappy`, release `1.3.1`, commit
`9c28114a38866f6deeaa826db918293bc28ae410`. The canonical license is
`upstream/COPYING`. `upstream/pristine/` holds the seven source and
header files. `SHA256SUMS` covers the license and every pristine file.
A normal build does not use the network. The package does not carry a
Lean parser for a unified diff. The verifier copies only `pristine/`,
applies `patches/0001-block-only.patch` with `git apply`, and requires
the result to equal `native/vendor/snappy/`. The pristine control and
the patched define-disabled build use matched configuration. The
production build defines `LEANP2P_SNAPPY_BLOCK_ONLY`. The native
compile uses `-Wall`, `-Wextra`, and `-Werror`, disables exceptions and
RTTI, and enables function and data sections. GCC 15 diagnoses ignored
alignment attributes on the upstream `std::pair<__m128i, __m128i>`
construct. Upstream `snappy.cc` adds `-Wno-ignored-attributes` after
`-Werror`. The diagnostic is suppressed only while compiling that file.
Every other warning remains an error. `snappy-sinksource.cc`,
`shim.cpp`, and the check drivers keep full `-Werror`. The upstream
source and the SIMD behavior remain unchanged. This narrow suppression
satisfies the repository warning-free build requirement. The pinned
source stays unpatched. The audit reads every
object and the archive. Omitting `snappy-stubs-internal.cc` stands only
when those objects link and the audit finds no missing required symbol.
The package architecture states the layout and the three builds.

## Native boundary command

A disposable Lake script showed three facts. A namespaced script can
run a native command. The script can find its package build directory.
A nonzero native exit becomes the Lake exit code. That script did not
link a production archive.

The Unit 1 command links the exact patched upstream-core archive
produced by the helper. It proves Lake archive linkage and core block
behavior. It does not exercise the later Lean shim ABI. Phase 3A adds
the compression shim to that archive and reruns the boundary and symbol
gates. Phase 3B extends the same gate for decompression. The driver
never recompiles a duplicate copy of production objects. A driver
failure fails the command. The production shim has no test counter and
no mutable test state. The helper commit records the stable command
name. If that link cannot be expressed cleanly, the shim, the private
extern, the public wrapper, and the first Lean test land in one commit.
No checkpoint leaves an untested shim.

## Test matrix

Lean cases live in `Tests/Snappy.lean`. `Tests/Main.lean` imports that
module and runs it before the summary. Checks use `failsWith` and
`succeedsWith`. A real failure makes `lake test` exit nonzero.

### Correctness

The cases are empty input, one byte, short text, repetitive bytes,
incompressible deterministic bytes, binary input that contains zero
bytes, sizes around the block boundaries, a larger input that spans
more than one upstream block, and generated round trips. Phase 3B runs
the first public round trips. Phase 4B holds the larger generated
suite. For each generated `x`:

```text
if compress x = .ok c, then decompress c x.size = .ok x
```

### Interoperability

The suite decodes known raw blocks. Fixtures from Go Snappy v0.0.4 are
generated independently and committed. Go decodes representative output
from this implementation, and that result is committed with the
fixtures. `lake test` reads the committed files. It does not run Go,
and it does not use the network. The fixtures are raw blocks. None is a
framed stream.

Compressed bytes from this native version may be pinned as regression
evidence. They are not a canonical public output. Decoding and a
successful round trip are the stable semantic contract.

### Invalid and hostile input

The cases are a truncated header, an invalid or overflowing encoded
length, a truncated payload, truncated copy operands, an invalid copy
offset, a malformed literal or copy encoding, a corrupted block, an
advertised length above the cap, an extreme expansion ratio, and a
repeated invalid call. When the advertised
length exceeds the cap, that result is `.outputTooLarge` even if the
payload is also invalid.

### Ownership and resources

A borrowed input is unchanged. Success and failure are repeated. The
production shim has no counter and no mutable test state. Output is
allocated only after the checks. The local symbol audit covers every
object and the archive. The Linux x86-64 audit and the paired sanitizer
runs are the Phase 4C job.

### Cap conversion

The cases are an exact small cap, a cap one byte below the required
size, a cap equal to `2^32`, and a boxed `Nat` such as `2^64`. The
large caps clamp. They do not narrow to zero, and they do not allocate
from that `Nat`. No cap case allocates a multi-gigabyte buffer. The
compression limit is `Snappy.Internal.inputWithinLimit`, which
`compress` calls. The suite calls that predicate with `2^32 - 1`,
`2^32`, and `2^64`. It builds no `ByteArray` of those sizes. `2^64`
narrows to zero under `Nat.toUInt32`, and the predicate still rejects
it. The shim repeats the check on `size_t` before it narrows the
length. That native check has no test hook.

## Fixtures and oracles

Every reference fixture records its provenance. A fixture produced only
by this package does not validate the package. Go fixtures pin
`github.com/golang/snappy` v0.0.4. Generation may use Go outside
`lake test`. The committed fixtures are what the suite reads. A normal
build and a normal test stay offline. A later pure Lean compressor may
emit different valid compressed bytes. Decoding and the round trip stay
the public contract. Exact bytes from `google/snappy` are regression
evidence for this native backend. They are not a claim that every
correct compressor emits those bytes.

## Acceptance commands

The repository gates are:

```text
lake build
lake test
lake test -- +RTS -N1 -RTS
scripts/lint-imports.sh
scripts/vendor-pull.sh --verify
python3 scripts/extract-vectors.py
```

`git diff --check` passes, and `Tests/vectors` is clean after the
extractor runs.

The helper records these stable commands:

```text
lake build snappyNative/snappyBoundary
lake build snappyNative/snappyAbort
lake build snappyNative/snappyAudit
lake build snappyNative/snappyValidation
```

`snappyBoundary` matches the three raw-block transcripts.
`snappyAbort` requires status 86 from each guarded call.
`snappyAudit` reads the production objects and archive, and it compares
the pristine and define-disabled symbol surfaces. `snappyValidation`
runs those three checks on the same production archive. The local audit
is macOS ARM64. The Linux x86-64 audit, ASan, LSan, and the
Snappy-free control passed in the warning-free CI run. The acceptance
record cites that run. These commands and that job complete W6.2.

## Risks

| Risk | Mitigation |
|---|---|
| The Lake 4.34 path helper does not link the upstream-core archive into the boundary command | Phase 2C links the driver to the patched upstream-core archive from the helper. If that link cannot be expressed, the shim, the extern, the wrapper, and the first test land together. |
| `lake update` rewrites `lake-manifest.json` | Phase 2C includes the manifest only when the update changes it, and the diff is part of the review. |
| The private extern spelling or the pair layout differs under Lean 4.34 | Phase 3A compiles the extern. A spelling change keeps the public signatures in the architecture. |
| A borrowed `ByteArray` is treated as owned | The extern uses `@&`, the shim takes `b_lean_obj_arg`, and a test checks that the input bytes are unchanged. |
| Decompressed output is allocated before the cap check | Phase 3B requires the shim to validate the advertised length and compare the clamped cap before allocation. |
| Unused upstream code keeps a live C++ runtime reference | Phase 2B guards those paths. The object and archive audits in Phase 2C and Phase 4C reject the forbidden references. |
| Dead stripping differs between macOS and Linux | Section flags stay on. The local audit and the Phase 4C x86-64 audit both read every object and the archive. |
| Platform feature macros drift between the three builds | The build-support headers state the choices. The pristine control and the define-disabled build use one matched configuration. The interoperability cases cover each production configuration. |
| An upstream assertion fires on hostile input | Malformed input returns `.invalidCompressedData`. The shim does not aim that input at an assertion. Phase 4A holds the hostile cases. |
| The patch and `native/vendor/snappy/` diverge | Phase 2B rebuilds the tree with `git apply` and compares it byte for byte. |
| ASan or LSan reports a Lean or GMP initialization leak | Phase 4C requires the Snappy executable and the matched runtime control to exit with no leak report. A leak in either executable fails the job. |
| W1.2 has landed | The public surface stays `ByteArray` and `Snappy.Error`. Production `Snappy.lean` does not import `Bytes`. |

## W6.3

W6.3 imports only `Snappy`. It chooses the output caps for its
protocols. It owns SSZ, the outer uncompressed-length protobuf varint,
the framed-stream chunks, and the masked CRC32C. It maps `Snappy.Error`
into its own protocol error at its boundary. It does not depend on a
native status, a native symbol, the helper package, the workspace, or
the patch layout. `compress`, `decompress`, and the
bounded-decompression tests have passed, so it can start on this API.

## Definition of done

W6.2 is complete when all of the following hold.

- The committed public API matches the architecture.
- Raw compression and bounded decompression work.
- A predictable input or limit failure uses one of the three
  `Snappy.Error` constructors.
- The shim enforces the output cap before allocation.
- Inputs are borrowed and remain unchanged.
- Outputs are new Lean-owned arrays.
- The pin, the license, the hashes, the patch, and the compiled tree
  verify offline.
- Every upstream behavioral change is guarded by
  `LEANP2P_SNAPPY_BLOCK_ONLY`.
- A class-specific `operator delete` aborts, and a fallback virtual
  body aborts.
- An unknown status panics, and an impossible reported compression
  length panics.
- The production objects and the archive have no forbidden live C++
  runtime reference.
- The known vectors, the generated round trips, the malformed inputs,
  the cap cases, the interoperability fixtures, and the stress tests
  pass.
- The Linux x86-64 symbol checks pass.
- The paired sanitizer and control checks pass.
- A normal build and `lake test` use no network.
- The existing suite and the import lint stay green.
- The CI workflow passes, including the Phase 4C job.
- The package states no axiom and no theorem that equates the native
  library with a pure model.
- W6.3 can call `compress` and `decompress` without importing the
  helper or the shim.

An implementation unit stays open until its evidence exists. Units 0
through 4 have that evidence.
