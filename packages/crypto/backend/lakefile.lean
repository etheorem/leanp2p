/-
The `crypto/backend` package: one of the package-local Lake helpers of
the repository (root ARCHITECTURE §2).

The declarative `lakefile.toml` cannot compile a C file. The shim
`c/p2pcrypto.c` needs a `buildO` target and pkg-config discovery of the
OpenSSL headers (CLAUDE.md, "Configure, don't integrate", and
docs/ARCHITECTURE.md, "Modules"). So this directory is a nested Lake
package, and the root `lakefile.toml` requires it by path. The root
stays declarative. This file holds only what the TOML form cannot say.

The shim compiles against the system OpenSSL 3 headers. It links
against the toolchain's own static `libcrypto.a`, which Lake links into
every executable. So the runtime library is the OpenSSL 3 that
`lean-toolchain` pins, and the shim needs no link argument. Do not add
a system `-L`: with it, the bundled `lld` finds the system C library
ahead of the toolchain's glibc, and the link fails.
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

/-- The system OpenSSL version that pkg-config reports, as one string. -/
unsafe def opensslVersion : String :=
  " ".intercalate (runPkgConfig #["--modversion", "libcrypto"]).toList

/-- The OpenSSL `-I` flags. The array is empty when the headers are on
the default include path. -/
unsafe def opensslCFlags : Array String := runPkgConfig #["--cflags", "libcrypto"]

/-- The hint the shim target fails with when pkg-config finds no
OpenSSL 3 headers. -/
def opensslMissing (found : String) : String :=
  s!"OpenSSL 3 headers not found through pkg-config (found: '{found}'): install \
  pkg-config and the OpenSSL 3 development package (Debian/Ubuntu: libssl-dev; \
  Fedora: openssl-devel; Gentoo: dev-libs/openssl; macOS: brew install openssl@3 \
  pkg-config)"

package Backend

-- `buildO` hashes `traceArgs` into the trace and leaves `weakArgs` out.
-- The portable flags go in the trace, so a flag change rebuilds. The
-- discovered include paths change from host to host, and they do not
-- change what the code means, so they stay out.
target p2pcrypto.o pkg : FilePath := do
  let version := unsafe opensslVersion
  unless version.startsWith "3." do error (opensslMissing version)
  let src := pkg.dir / "c" / "p2pcrypto.c"
  let obj := pkg.buildDir / "c" / "p2pcrypto.o"
  let weak := #["-I", (← getLeanIncludeDir).toString] ++ unsafe opensslCFlags
  buildO obj (← inputTextFile src) weak #["-fPIC", "-O2", "-Wall", "-Werror"] "cc" getLeanTrace

-- The archive crosses the `require` to the root. Lake links every
-- `extern_lib` of a required package into every executable of the
-- workspace, whether or not a module of the executable imports it.
extern_lib libleanp2p_backend pkg := do
  let lib := pkg.staticLibDir / nameToStaticLib "leanp2p_backend"
  buildStaticLib lib #[← p2pcrypto.o.fetch]

@[default_target]
lean_lib Backend where
  roots := #[`Backend]
  globs := #[.andSubmodules `Backend]
