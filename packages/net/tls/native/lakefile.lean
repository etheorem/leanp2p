/-
The `net/tls` native package: the libssl shim `c/tls_shim.c` and its
`@[extern]` bindings, `TlsNative.lean`.

The declarative `lakefile.toml` cannot compile a C file (CLAUDE.md,
"Configure, don't integrate"), so this directory is a nested Lake
package, as `crypto/backend` is, and the root `lakefile.toml` requires
it by path. The shim compiles against the system OpenSSL 3 headers,
which pkg-config finds. It links against the toolchain's own static
`libssl.a` and `libcrypto.a`, which Lake links into every executable,
so the runtime library is the OpenSSL that `lean-toolchain` pins, and
the shim needs no link argument. The backend's lakefile records why a
system `-L` must stay out.
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

package TlsNative

-- `buildO` hashes `traceArgs` into the trace and leaves `weakArgs` out.
-- The discovered include paths change from host to host, and they do
-- not change what the code means, so they stay out of the trace.
target tls_shim.o pkg : FilePath := do
  let src := pkg.dir / "c" / "tls_shim.c"
  let obj := pkg.buildDir / "c" / "tls_shim.o"
  let weak := #["-I", (← getLeanIncludeDir).toString] ++ unsafe opensslCFlags
  let header := pkg.dir / "c" / "tls_shim.h"
  buildO obj (← inputTextFile src) weak #["-fPIC", "-O2", "-Wall", "-Werror"] "cc"
    (extraDepTrace := do
      addTrace (← computeTrace (TextFilePath.mk header))
      addTrace (← getLeanTrace)
      return BuildTrace.nil)

-- Lake links every `extern_lib` of a required package into every
-- executable of the workspace.
extern_lib libleanp2p_tls pkg := do
  let lib := pkg.staticLibDir / nameToStaticLib "leanp2p_tls"
  buildStaticLib lib #[← tls_shim.o.fetch]

@[default_target]
lean_lib TlsNative where
  roots := #[`TlsNative]
