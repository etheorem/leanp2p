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

W1.2 and W2.1 are still open. Their isolated executable mocks carry
the dependency assumptions, as RULES.md permits. The package docs
state the integration boundary.
-/
