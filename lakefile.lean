import Lake
open Lake DSL

package «leanp2p»

/-- Debian/Ubuntu multiarch directory of the host (for the libc headers and
`libcrypto`), derived from the platform triple (`x86_64-...-linux-gnu`).
Environment requirement of the phase 2 crypto shim: the toolchain compiles
C with `-nostdinc --sysroot <toolchain>` and glibc's arch-specific headers
(`bits/`, `gnu/`) live under `/usr/include/<multiarch>` on Debian/Ubuntu
(where CI runs); on other layouts adjust this and the `libcrypto` path
below. -/
def hostMultiarch : String :=
  s!"{System.Platform.target.takeWhile (· != '-')}-linux-gnu"

/-- The OpenSSL FFI shim (`c/p2pcrypto.c`, phase 2 step 11), compiled with
the Lean toolchain's C compiler. `-isystem /usr/include` (and the multiarch
dir) is needed because the toolchain compiles C with
`-nostdinc --sysroot <toolchain>`, which hides the libc headers. -/
target p2pcryptoO (pkg : NPackage __name__) : System.FilePath := do
  let srcJob ← inputTextFile (pkg.dir / "c" / "p2pcrypto.c")
  buildLeanO (pkg.buildDir / "c" / "p2pcrypto.o") srcJob
    #["-isystem", "/usr/include", "-isystem", s!"/usr/include/{hostMultiarch}"]

@[default_target]
lean_lib «LeanP2P»

@[default_target]
lean_exe «demo» where
  root := `Main
  moreLinkObjs := #[p2pcryptoO]
  -- Full path on purpose: the toolchain links its own bundled glibc, and an
  -- extra `-L/usr/lib/...` here would redirect `-lc` to the system libc and
  -- break the link (__libc_csu_init is gone in glibc >= 2.34).
  moreLinkArgs := #[s!"/usr/lib/{hostMultiarch}/libcrypto.so.3"]

/-- The phase 4 interop node (scripts/ping-interop.sh, go loopback ping). -/
lean_exe «pingnode» where
  root := `PingNode
  moreLinkObjs := #[p2pcryptoO]
  moreLinkArgs := #[s!"/usr/lib/{hostMultiarch}/libcrypto.so.3"]

/-- The phase 5 transport-interop harness (VECTOR_TEST_PLAN.md step 25;
libp2p/test-plans transport-interop shape, scripts/interop-matrix.sh). -/
lean_exe «interop» where
  root := `Interop
  moreLinkObjs := #[p2pcryptoO]
  moreLinkArgs := #[s!"/usr/lib/{hostMultiarch}/libcrypto.so.3"]

@[default_target]
lean_lib «Tests» where
  globs := #[.submodules `Tests]

/-- `lake test` builds and runs the vector suites (VECTOR_TEST_PLAN.md,
phase 0 step 3). Vector JSON is read from `Tests/vectors` relative to the
working directory; override with `LEANP2P_VECTORS`. -/
@[test_driver]
lean_exe «tests» where
  root := `Tests.Main
  moreLinkObjs := #[p2pcryptoO]
  moreLinkArgs := #[s!"/usr/lib/{hostMultiarch}/libcrypto.so.3"]
