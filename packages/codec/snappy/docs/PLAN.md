# leanp2p snappy: plan

This plan refines root unit W6.2 for `codec/snappy`. The root plan owns
order across packages, and the package architecture owns the contracts.
This file records the completed implementation units, validation gates,
and acceptance evidence.

## Root unit and scope

W6.2 is P0. It depends on W1.2, and W1.2 has landed.

Production code uses the prelude `ByteArray` and the package inductive
`Snappy.Error`. Production `Snappy.lean` does not import `Bytes`.
Tests may import `Bytes`. That import adds no production dependency.

The package owns raw Snappy block compression and bounded
decompression. SSZ, req/resp framing, the outer length varint, framed
chunks, CRC32C, and networking stay outside this package.

## Implementation units

Units 0 through 4 are complete.

| Unit | Deliverable | Completion evidence |
|---|---|---|
| 0 | The contracts and this plan | The root documents and this plan agree. |
| 1 | Provenance and the native build | The ordinary build is offline. The verifier rebuilds the compiled tree. |
| 2 | Raw block compression | `compress`, the shim, and the compression tests are present. |
| 3 | Bounded raw block decompression | `decompress` enforces the output cap before allocation. |
| 4 | Interoperability, hostile input, and native hardening | The suite and the Linux x86-64 hardening job pass. |

## Public surface

```lean
namespace Snappy

inductive Error
  | inputTooLarge
  | invalidCompressedData
  | outputTooLarge

compress : ByteArray → Except Error ByteArray
decompress : ByteArray → Nat → Except Error ByteArray

end Snappy
```

`Snappy.Internal.inputWithinLimit` is unsupported. Callers use
`compress`.

## Upstream provenance and build

The pin is `https://github.com/google/snappy`, release 1.3.1, commit
`9c28114a38866f6deeaa826db918293bc28ae410`. The canonical license is
`upstream/COPYING`. `upstream/SHA256SUMS` covers the license and the
seven pristine sources and headers.

`upstream/pristine/` holds those files.
`patches/0001-block-only.patch` places every behavioral change under
`LEANP2P_SNAPPY_BLOCK_ONLY`. `scripts/verify-upstream.py` copies the
pristine tree, applies that patch with `git apply`, and requires a
byte-for-byte match with `native/vendor/snappy/`.

The helper builds three matched configurations. The pristine control
and the patched build without the define share one configuration.
The production build defines `LEANP2P_SNAPPY_BLOCK_ONLY` and emits
one static archive from that core and the shim. The block build
omits `snappy-stubs-internal.cc`; successful linkage and the symbol
audit validate that omission.

The native compile uses `-Wall`, `-Wextra`, and `-Werror`. It disables
exceptions and RTTI, and it enables function and data sections. GCC 15
diagnoses ignored alignment attributes in upstream `snappy.cc`. That
translation unit adds `-Wno-ignored-attributes` after `-Werror`. Every
other warning remains an error. The sink, the shim, and the check
drivers keep full `-Werror`. The pinned source and its SIMD behavior
stay unchanged. The package architecture explains the diagnostic.

A normal build and `lake test` use no network.

## Safety and native hardening

The private externs take a borrowed `@& ByteArray`. The shim receives
`b_lean_obj_arg`. A borrowed input is unchanged after the call. Each
successful output is a new Lean-owned array.

`decompress` reads the advertised uncompressed length and compares it
with the clamped cap before allocation. A cap of `2^32` or greater
clamps to the largest length the raw format can store. The call does
not allocate from the original `Nat`.

An unknown native status calls `leanp2p_snappy_internal_panic`. An
impossible reported compression length does the same.
`snappyInternalPanic` checks that path. A class-specific
`operator delete` aborts, and a fallback virtual body aborts. Both are
guarded by `LEANP2P_SNAPPY_BLOCK_ONLY`. `snappyAbort` requires status
86 from each guarded call.

The production archive members are `snappy.block.o`,
`snappy-sinksource.block.o`, and `shim.o`. The shim exports
`leanp2p_snappy_compress`, `leanp2p_snappy_decompress`, and
`leanp2p_snappy_internal_panic`. `snappyAudit` reads every production
object and the archive. It rejects a live `std::` runtime reference,
a global `operator new`, a global `operator delete`, `__cxa_*`, and
`__gxx_personality*`. The pristine and define-disabled symbol surfaces
match.

`snappyBoundary` links each archive from the helper and runs the
raw-block driver on that archive. The driver checks core block
behavior. It does not exercise the Lean shim ABI, and it does not
compile a second copy of the production objects. The shim has no test
counter and no mutable test state.

On Linux x86-64, `snappy-native-hardening` compares the Snappy
executable with a Snappy-free control. The unsanitized dynamic
libraries match, and both dynamic C++ runtime sets are empty. The
sanitized sets match, and both link `libasan`. The job links no second
C++ runtime. The ASan runs are clean, and the LSan runs are clean. A
leak report from either executable fails the job. The negative
controls report `heap-use-after-free` and a LeakSanitizer leak.

## Tests and interoperability

`Tests/Snappy.lean` holds the Lean cases. `Tests/Main.lean` runs that
module before the summary. A failed check makes `lake test` exit
nonzero.

### Correctness and boundaries

The suite covers an empty block, one byte, short text, repetitive
bytes, incompressible deterministic bytes, and binary input that
contains a zero byte. It covers literal and copy boundaries, a 64 KiB
block, and input that spans more than one block. It also runs the
generated public round trips and repeats calls.

For each generated `x`:

```text
if compress x = .ok c, then decompress c x.size = .ok x
```

That check is an executable property test. No theorem equates the FFI
with a pure model.

### Invalid and hostile input

The suite rejects a truncated header, an invalid or overflowing
length, a truncated payload, truncated copy operands, an invalid copy
offset, a malformed literal or copy encoding, and a corrupted block.
A framed-stream identifier returns `invalidCompressedData`. When the
advertised length exceeds the cap, the result is `outputTooLarge`,
including when the payload is also invalid. The suite covers an
extreme expansion ratio and repeats invalid calls.

### Ownership and resource limits

A borrowed input still matches its snapshot after the call. The suite
repeats success, then failure, then success.

The cap cases are an exact cap, a cap one byte short, a zero cap, a
cap of `2^32`, and a boxed `Nat` cap of `2^64`. The large caps clamp.
No cap case allocates a multi-gigabyte buffer. The suite checks
`Snappy.Internal.inputWithinLimit` at `2^32 - 1`, `2^32`, and `2^64`,
and it builds no `ByteArray` of those sizes. `2^64` narrows to zero
under `Nat.toUInt32`, and the predicate still rejects it. The shim
repeats the length check on `size_t` before it narrows. That native
check has no test hook.

### Independent interoperability

The Go fixture module is `leanp2p/snappy-go-fixtures`. It requires
`github.com/golang/snappy` v0.0.4 and has no replace directive.
`Tests/fixtures/snappy-go-v0.0.4.json` records that provenance. The
generator may run outside `lake test`. The suite reads the committed
file. It does not run Go, and it does not use the network.

The fixtures are raw blocks. Lean decompresses the Go `Encode` bytes.
Go `Decode` accepts the named native regressions, and those results
are committed with the fixture. Exact compressed bytes are named
backend regressions. They are not the general public contract.
Decoding and a successful round trip are the stable contract.

## Platform evidence

| Platform | Evidence |
|---|---|
| macOS ARM64 | Both `lake test` runs report 9208 passed, 0 failed, 0 todo, and 2 skipped. The skips need `/proc/self/status`. Native validation passed. |
| Linux x86-64 | [CI run 41710650445](https://github.com/etheorem/leanp2p/actions/runs/41710650445) is green. Both `lake test` runs report 9211 passed, 0 failed, 0 todo, and 0 skipped. Native compilation completed with no compiler warnings. The symbol and dependency audit passed. ASan and LSan passed. |
| Linux ARM64 | This check is best-effort and does not gate P0. Snappy validation passed, and root `lake build` passed. Root `lake test` stopped because `packages/crypto/backend/c/p2pcrypto.c` requires `OSSL_SIGNATURE_PARAM_NONCE_TYPE`, which Ubuntu 24.04 OpenSSL 3.0.13 does not provide. Complete Linux ARM64 support is not claimed. |

The trust boundary is empirical. The Lean kernel does not check the
native bytes. The package states no axiom and no theorem that equates
the native implementation with a pure model.

## Acceptance commands

```text
lake build
lake test
lake test -- +RTS -N1 -RTS
scripts/lint-imports.sh
git diff --check
scripts/vendor-pull.sh --verify
python3 scripts/extract-vectors.py
python3 packages/codec/snappy/scripts/verify-upstream.py
lake build snappyNative/snappyBoundary
lake build snappyNative/snappyAbort
lake build snappyNative/snappyInternalPanic
lake build snappyNative/snappyAudit
lake build snappyNative/snappyValidation
```

These commands pass, and vector extraction leaves `Tests/vectors`
unchanged. The Linux x86-64 CI run above is green.

## W6.3 integration

W6.3 imports only `Snappy`. It chooses the protocol-specific output
caps. It owns SSZ, req/resp framing, the outer length varint, framed
chunks, CRC32C, and networking behavior. It maps `Snappy.Error` into
its own protocol errors. It does not depend on a native symbol, a
helper target, the workspace layout, or the patch structure. A later
pure Lean body can replace the native body behind the same signatures.

The documented API and the bounded-decompression tests are ready for
W6.3.

## Definition of done

W6.2 is complete. These gates hold.

- The public API matches the architecture.
- Raw compression and bounded decompression work.
- Predictable input and limit failures use one of the three
  `Snappy.Error` constructors.
- Inputs are borrowed, outputs are new Lean-owned arrays, the output
  cap is enforced before allocation, and impossible native states panic.
- The offline pin, patch, and compiled tree verify.
- The guarded deletes and fallback bodies abort.
- The test, interoperability, and Linux x86-64 hardening checks pass.
- The package and its tests contain no `sorry`.
- Native compilation completes with no compiler warnings.
- A normal build and `lake test` use no network.
- The import lint stays green.
- The package states no axiom or theorem equating the native implementation
  with a pure model.
- CI passes, including `snappy-native-hardening`.
- W6.3 can call the public functions without importing the helper or
  the shim.

These gates complete W6.2.
