import Varint.UVarint
import Varint.Theorems
import Varint.Bytes

/-!
# Varint

The unsigned varint codec (ARCHITECTURE §4.3). This root module
re-exports the public submodules of `codec/varint`:

- `Varint.UVarint`: the proof-carrying `UVarint` newtype, the 9-byte
  budget constant, the model core `encode` and `decode?`, and the
  `Codec UVarint` and `LawfulCodec UVarint` instances.
- `Varint.Theorems`: the budget lemma, the suffix round-trip theorem,
  the accepted-input split, and the concrete rejection theorems.
- `Varint.Bytes`: the production `ByteArray` entry points `encodeB` and
  `decodeB?` and their model bridge theorems.
-/
