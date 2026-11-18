/-
The `net/quic` native package: ngtcp2, its OpenSSL glue
(`crypto_ossl`), the shim `c/quic_shim.c`, and the `@[extern]`
bindings, `QuicNative.lean`.

The declarative `lakefile.toml` cannot compile C (CLAUDE.md, "Configure,
don't integrate"), so this directory is a nested Lake package, as
`crypto/backend` and `net/tls/native` are, and the root `lakefile.toml`
requires it by path.

ngtcp2 compiles from the pinned tree `../upstream/pristine/`, the files
of the v1.24.0 tag that the library and `crypto_ossl` need, byte for
byte (`../upstream/UPSTREAM.toml`, `../upstream/SHA256SUMS`,
`../scripts/verify-upstream.py`). No patch applies, so the pinned tree
is the compiled tree. `include/` holds the two build-support headers
that CMake would write: `config.h` and `ngtcp2/version.h`. The static
archive resolves every OpenSSL call to the toolchain's own `libssl.a`
and `libcrypto.a`, which Lake links into every executable. So the
process holds one OpenSSL, the one `lean-toolchain` pins, and the
system's ngtcp2 and libssl stay out (the package ARCHITECTURE, "The
native build").
-/
import Lake
open Lake DSL System

/-- `pkg-config <args>` at configuration load, split on whitespace. The
empty array stands for every failure: no pkg-config, a nonzero exit, or
empty output. -/
unsafe def runPkgConfig (args : Array String) : Array String :=
  Id.run <| unsafeBaseIO do
    match ← (IO.Process.output { cmd := "pkg-config", args }).toBaseIO with
    | .ok r =>
      if r.exitCode != 0 then return #[]
      return (r.stdout.trimAscii.toString.splitOn " ").toArray.filter (!·.isEmpty)
    | .error _ => return #[]

/-- The OpenSSL `-I` flags. The array is empty when the headers are on
the default include path. -/
unsafe def opensslCFlags : Array String := runPkgConfig #["--cflags", "libssl"]

/-- The pinned ngtcp2 tree. -/
def pristine (pkg : Package) : FilePath :=
  pkg.dir / ".." / "upstream" / "pristine"

/-- The units of the library, relative to `lib/` of the pinned tree:
the `ngtcp2_SOURCES` list of the upstream `lib/CMakeLists.txt` at the
pin, in its order. -/
def libSources : Array String := #[
  "ngtcp2_pkt.c", "ngtcp2_conv.c", "ngtcp2_str.c", "ngtcp2_vec.c", "ngtcp2_buf.c",
  "ngtcp2_conn.c", "ngtcp2_mem.c", "ngtcp2_pq.c", "ngtcp2_map.c", "ngtcp2_rob.c",
  "ngtcp2_ppe.c", "ngtcp2_crypto.c", "ngtcp2_err.c", "ngtcp2_range.c", "ngtcp2_acktr.c",
  "ngtcp2_rtb.c", "ngtcp2_frame_chain.c", "ngtcp2_strm.c", "ngtcp2_idtr.c", "ngtcp2_gaptr.c",
  "ngtcp2_ringbuf.c", "ngtcp2_log.c", "ngtcp2_qlog.c", "ngtcp2_cid.c", "ngtcp2_ksl.c",
  "ngtcp2_cc.c", "ngtcp2_bbr.c", "ngtcp2_addr.c", "ngtcp2_path.c", "ngtcp2_pv.c",
  "ngtcp2_pmtud.c", "ngtcp2_version.c", "ngtcp2_rst.c", "ngtcp2_wf.c", "ngtcp2_opl.c",
  "ngtcp2_balloc.c", "ngtcp2_objalloc.c", "ngtcp2_unreachable.c", "ngtcp2_transport_params.c",
  "ngtcp2_settings.c", "ngtcp2_callbacks.c", "ngtcp2_dcidtr.c", "ngtcp2_pcg.c",
  "ngtcp2_ratelim.c", "ngtcp2_conn_info.c", "ngtcp2_fmt.c"]

/-- The include paths of every unit: the build-support headers first,
so `ngtcp2/version.h` resolves there, then the pinned headers, the TLS
shim's header, the Lean header, and OpenSSL's. The paths stay out of the
trace (`weakArgs`); the headers' bytes enter it through `headerTrace`. -/
def includeArgs (pkg : Package) (leanInclude : FilePath) : Array String :=
  let v := pristine pkg
  #["-I", (pkg.dir / "include").toString,
    "-I", (v / "lib" / "includes").toString,
    "-I", (v / "lib").toString,
    "-I", (v / "crypto" / "includes").toString,
    "-I", (v / "crypto").toString,
    "-I", (pkg.dir / ".." / ".." / "tls" / "native" / "c").toString,
    "-I", leanInclude.toString] ++ unsafe opensslCFlags

/-- The flags of the pinned units: the defines that the upstream CMake
build sets for a static library (`HAVE_CONFIG_H`, `BUILDING_NGTCP2`,
`NGTCP2_STATICLIB`), and no `-Werror`. The sources are upstream's, and
a new compiler's warning in them must not stop the build. -/
def vendorArgs : Array String :=
  #["-fPIC", "-O2", "-DHAVE_CONFIG_H", "-DBUILDING_NGTCP2", "-DNGTCP2_STATICLIB"]

/-- The flags of the shim: every warning is an error, as in the other
shims. -/
def shimArgs : Array String :=
  #["-fPIC", "-O2", "-Wall", "-Werror", "-DNGTCP2_STATICLIB"]

/-- The trace of the headers every unit includes: the build-support
headers, the public headers of the pinned tree, and the TLS shim's
header. The private headers of the pinned tree change only with the
pin, which `scripts/verify-upstream.py` checks. -/
def headerTrace (pkg : Package) : FetchM BuildTrace := do
  let v := pristine pkg
  let headers := #[pkg.dir / "include" / "config.h", pkg.dir / "include" / "ngtcp2" / "version.h",
    v / "lib" / "includes" / "ngtcp2" / "ngtcp2.h",
    v / "crypto" / "includes" / "ngtcp2" / "ngtcp2_crypto.h",
    v / "crypto" / "includes" / "ngtcp2" / "ngtcp2_crypto_ossl.h",
    pkg.dir / ".." / ".." / "tls" / "native" / "c" / "tls_shim.h"]
  let mut t := BuildTrace.nil
  for h in headers do
    t := t.mix (← computeTrace (TextFilePath.mk h))
  return t

package QuicNative

-- `QuicNative.lean` names the TLS context type of `net/tls`.
require TlsNative from ".." / ".." / "tls" / "native"

/-- Compile one unit. -/
def compileUnit (pkg : Package) (src obj : FilePath) (args : Array String) :
    FetchM (Job FilePath) := do
  let weak := includeArgs pkg (← getLeanIncludeDir)
  let hdrs ← headerTrace pkg
  buildO obj (← inputTextFile src) weak args "cc" (extraDepTrace := do
    addTrace hdrs
    addTrace (← getLeanTrace)
    return BuildTrace.nil)

-- Lake links every `extern_lib` of a required package into every
-- executable of the workspace.
extern_lib libleanp2p_quic pkg := do
  let v := pristine pkg
  let out := pkg.buildDir / "c"
  let mut jobs : Array (Job FilePath) := #[]
  for src in libSources do
    jobs := jobs.push (← compileUnit pkg (v / "lib" / src) (out / "lib" / (src ++ ".o")) vendorArgs)
  jobs := jobs.push (← compileUnit pkg (v / "crypto" / "shared.c") (out / "shared.c.o") vendorArgs)
  jobs := jobs.push (← compileUnit pkg (v / "crypto" / "ossl" / "ossl.c") (out / "ossl.c.o") vendorArgs)
  jobs := jobs.push (← compileUnit pkg (pkg.dir / "c" / "quic_shim.c") (out / "quic_shim.c.o") shimArgs)
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanp2p_quic") jobs

@[default_target]
lean_lib QuicNative where
  roots := #[`QuicNative]
