import Bytes.Error
import Bytes.Codec
import Bytes.Model
import Bytes.Text
import Bytes.Harness
import Bytes.Take
import Bytes.Blob

/-!
# Bytes

The byte floor of the stack (ARCHITECTURE §4.2). It holds the
`List Nat` byte model and its conversions, the `Codec` and
`LawfulCodec` classes with the shared `DecodeError`, and the generic
round-trip harness that every later codec package runs.

The model exists for the proofs: the verified codec cores state their
theorems over `List Nat`, where `omega` closes the arithmetic, and the
harness pins each production `ByteArray` path to that model
(ARCHITECTURE §6). This root module re-exports the public submodules.
-/
