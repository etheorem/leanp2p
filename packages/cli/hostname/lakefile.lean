import Lake
open Lake DSL System

package InteropHostname

target interop_hostname.o pkg : FilePath := do
  let src := pkg.dir / "c" / "hostname.c"
  let obj := pkg.buildDir / "c" / "hostname.o"
  let weak := #["-I", (← getLeanIncludeDir).toString]
  buildO obj (← inputTextFile src) weak #["-fPIC", "-O2", "-Wall", "-Werror"] "cc" getLeanTrace

extern_lib libleanp2p_interop_hostname pkg := do
  let lib := pkg.staticLibDir / nameToStaticLib "leanp2p_interop_hostname"
  buildStaticLib lib #[← interop_hostname.o.fetch]

@[default_target]
lean_lib InteropHostname where
  roots := #[`InteropHostname]

lean_exe hostname_check where
  root := `HostnameCheck
