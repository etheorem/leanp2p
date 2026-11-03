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
-/
