import Proto.Wire
import Proto.Core
import Proto.Lookup
import Proto.Message
import Proto.Bytes

/-!
# Proto

The protobuf wire codec (ARCHITECTURE §4.5). The ordered Fields model
owns its bounds; the core proves both codec laws. Lookups and message
tables reuse that core. ByteArray decoding has its own cursor path.

The package imports the merged byte and varint implementations. Its
codec instances use the shared byte classes, and its proofs use the
varint theorems directly.
-/
