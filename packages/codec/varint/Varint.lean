import Varint.UVarint
import Varint.Theorems
import Varint.Bytes

/-!
# Varint

The unsigned varint codec (ARCHITECTURE §4.3): the `UVarint` newtype,
the model core over `List Nat` with its `LawfulCodec` instance, the
theorems, and the production `ByteArray` path. This root module
re-exports the public submodules. The package docs live under `docs/`
beside this file.

W1.2 is still open, so the package builds against the mock of
`base/bytes` in `Varint.Mock.Bytes` (RULES.md, "Working ahead of the
tree"). The mock is internal, and the root does not re-export it.
-/
