/-
The `net/streams` shim package: the C abort of `Streams.Tcp`, and the
platform's `ECONNRESET`.

The declarative `lakefile.toml` cannot compile a C file (CLAUDE.md,
"Configure, don't integrate"), so this directory is a nested Lake
package, as `crypto/backend` is, and the root `lakefile.toml` requires
it by path. The shim compiles against the toolchain's `lean.h` and
links against the `libuv.a` that the toolchain already links into every
executable, so it needs no system library.
-/
import Lake
open Lake DSL System

package StreamsShim

-- `buildO` hashes `traceArgs` into the trace and leaves `weakArgs` out.
target tcpabort.o pkg : FilePath := do
  let src := pkg.dir / "c" / "tcpabort.c"
  let obj := pkg.buildDir / "c" / "tcpabort.o"
  let weak := #["-I", (← getLeanIncludeDir).toString]
  buildO obj (← inputTextFile src) weak #["-fPIC", "-O2", "-Wall", "-Werror"] "cc" getLeanTrace

target tcperrno.o pkg : FilePath := do
  let src := pkg.dir / "c" / "tcperrno.c"
  let obj := pkg.buildDir / "c" / "tcperrno.o"
  let weak := #["-I", (← getLeanIncludeDir).toString]
  buildO obj (← inputTextFile src) weak #["-fPIC", "-O2", "-Wall", "-Werror"] "cc" getLeanTrace

-- Lake links every `extern_lib` of a dependency into the executables
-- that import it.
extern_lib libleanp2p_streams_shim pkg := do
  let lib := pkg.staticLibDir / nameToStaticLib "leanp2p_streams_shim"
  buildStaticLib lib #[← tcpabort.o.fetch, ← tcperrno.o.fetch]

@[default_target]
lean_lib StreamsShim where
  roots := #[`StreamsShim]
