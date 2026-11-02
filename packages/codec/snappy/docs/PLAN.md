# leanp2p snappy: plan

This plan refines root unit W6.2 for `codec/snappy`. The root plan owns
order across packages. The package architecture owns the contracts.
This file owns the units, the commit checkpoints, and the gates. A
checkpoint below is an unstaged diff. It is committed only after
review and an explicit approval. The next checkpoint waits until that
commit and its gates are accepted.

No implementation unit is complete. The documents do not count as a
working binding.

## Root unit

W6.2 is P0. Its root dependency is W1.2, `base/bytes`. W1.2 is still a
scaffold. The approved public surface uses the prelude `ByteArray` and
the package inductive `Snappy.Error`. The package does not import
`Bytes`. The root plan lets an implementer write against a frozen
signature before the dependency finishes (root PLAN, "How to read this
plan"). W1.2 stays a planning dependency and does not block the native
binding. When W1.2 lands, a shared helper may be adopted only when it
leaves the committed public surface unchanged.

W6.3 consumes this package after `compress`, `decompress`, and the
bounded-decompression tests exist. Until then W6.3 does not start on
this API.

## Units

| Unit | Deliverable | Done when |
|---|---|---|
| 0 | The root native-helper exception, the root pure-FFI allocation rule, the Snappy architecture, and this plan | The four documents are committed and agree. No implementation is claimed. |
| 1 | The pinned pristine `google/snappy` 1.3.1 sources, the canonical BSD license, the metadata and hashes, the guarded block-only patch, the committed patched tree, the offline verifier, the package-local Lake helper, the static archive of the patched upstream core, the three build controls, the native boundary command linked to that core archive, and the local object and archive audit | The ordinary build is offline. The verifier rebuilds the compiled tree exactly. The guarded-source gates and the local native-build gates pass. |
| 2 | `Snappy.Error`, the private compression extern, the compression shim, public `compress`, the input-size checks in Lean and in the shim, empty-input compression, known compression regressions, borrowed-input immutability, repeated deterministic compression, native compression-boundary validation, and the compression panics for an unknown status and an impossible result | The shim, the wrapper, and the durable tests land together. No commit contains an untested compression shim. |
| 3 | The private decompression extern, the cap conversion, the native length check before allocation, public `decompress`, the malformed and output-limit results, the minimal valid, malformed, exact-cap, and over-cap tests, and the first public round trips | The public surface in the architecture exists. The output cap is enforced before allocation. No commit contains an untested decompression shim. |
| 4 | The malformed-input matrix, the generated round trips, the Go fixtures, the repeated-call and ownership stress, the production archive audits, the Linux x86-64 run, the paired sanitizer runs, and the acceptance record | Every definition-of-done gate passes in CI. W6.3 can call the documented API. |

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
the compression shim to the Phase 2C archive and reruns the boundary
command and the symbol audit against that updated archive. A borrowed
input is unchanged. Empty input produces `0x00`. Known compression
regression cases pass, and repeated compression of the same input is
deterministic for the pinned backend. A length of at least `2^32` is
rejected in the wrapper and again in the shim, with no unsafe
narrowing. An unknown status and an impossible reported compressed
length panic. A failed test makes the process exit nonzero.

### Phase 3B. Bounded decompression

```text
feat(snappy): add bounded raw block decompression
```

The commit adds the decompression entry point, the private
decompression extern, the public cap conversion, public `decompress`,
and the minimal valid, malformed, and cap tests. The shim parses the
advertised length and compares it with the clamped cap before it
allocates. An exact cap succeeds. A smaller cap returns
`.outputTooLarge`. Invalid input returns `.invalidCompressedData`. A
cap of `2^32` or greater accepts every length the raw format can
store. An unknown native status panics in the wrapper. The first
end-to-end public round trips pass: if `compress x = .ok c`, then
`decompress c x.size = .ok x`. The commit adds the decompression shim
to the archive and reruns the boundary command and the symbol audit.

### Phase 4A. Invalid input

```text
test(snappy): cover malformed blocks and limits
```

The suite adds a truncated length header, an overlong or overflowing
length, a truncated payload, an invalid tag, an invalid copy offset, a
corrupted block, a declared output above the cap, an extreme expansion
ratio, and the case where the advertised length exceeds the cap before
the payload is fully validated.

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
ASan and LSan on the Snappy executable and the same pair on the
control. A leak is accepted only when the same stacks appear in the
control. The job links no second C++ runtime.

### Phase 4D. Acceptance record

```text
docs(snappy): record completed validation
```

This commit happens after the implementation and the CI evidence exist.
It records completion. It does not rewrite the architecture.

## Hardening

| Requirement | Checkpoint | Evidence |
|---|---|---|
| Aborting class-specific `operator delete`, with no no-op delete | Source in Phase 2B; compiled evidence in Phase 2C | Patch review in 2B. Define-enabled checks where they are safe, and the symbol audit, in 2C |
| Every upstream behavioral change under `LEANP2P_SNAPPY_BLOCK_ONLY` | Guards in Phase 2B; comparison in Phase 2C | The readable patch in 2B. The pristine and patched define-disabled comparison in 2C |
| Panic on an unknown status and on an impossible reported compression length | Phases 3A and 3B | Review of the Lean status map and of the native invariants, plus the ordinary-path tests |
| Deterministic vendor-patch verification | Phase 2B | Offline `git apply` and a byte-for-byte comparison |
| Linux x86-64 audit and a matched sanitizer control | Phase 4C | CI logs from a runner that asserts `x86_64` |

The Phase 2B source checks, the Phase 2C builds, and the Phase 3
evidence are local. The Phase 4C logs are CI-only. The repository
workflow on `ubuntu-latest` already runs `lake build`, `lake test`,
the single-capability run, the import lint,
and the vector provenance check. It does not yet run the Snappy symbol
audit or the paired sanitizers.

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
RTTI, and enables function and data sections. The audit reads every
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
length, a truncated payload, an invalid tag, an invalid copy offset, a
corrupted block, an advertised length above the cap, an extreme
expansion ratio, and a repeated invalid call. When the advertised
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
compression limit of `2^32` is not tested by building a `ByteArray` of
that size. That bound is closed by review of both checks and by a
focused native boundary check. The production shim gains no test hook
for it.

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

The helper also gains package-local commands for the offline source
verification, the pristine and define-disabled comparison, the
production boundary check, the object and archive audit, and the
sanitizer and control run. This plan does not name those commands. The
helper commit records the stable names here.

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
| ASan or LSan reports a Lean or GMP initialization leak | Phase 4C accepts a leak only when the same stacks appear in the matched Snappy-free control from the same job. |
| W1.2 lands after this work starts | The public surface stays `ByteArray` and `Snappy.Error`. A shared helper is adopted only when that surface stays unchanged. |

## W6.3

W6.3 imports only `Snappy`. It chooses the output caps for its
protocols. It owns SSZ, the outer uncompressed-length protobuf varint,
the framed-stream chunks, and the masked CRC32C. It maps `Snappy.Error`
into its own protocol error at its boundary. It does not depend on a
native status, a native symbol, the helper package, the workspace, or
the patch layout. It may start on this API after `compress`,
`decompress`, and the bounded-decompression tests pass.

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

An implementation unit stays open until its evidence exists.
