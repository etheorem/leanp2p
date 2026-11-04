/-!
# CLI build root

This nominal root exports no library API. Executable-specific code
lives under `CliApp`, so it does not collide with the maintained
parser dependency's `Cli` module. The two launchers own their `main`.
-/

set_option autoImplicit false
