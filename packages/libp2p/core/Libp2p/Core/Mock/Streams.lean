/-!
# Streams mock

Temporary `Connection`, `Connection.close`, and `Stream` interfaces
for W4.1 (#10). This module imports no real streams implementation
and adds no dependency axioms. See `docs/ARCHITECTURE.md`, "The mocks",
for integration steps.
-/

set_option autoImplicit false

namespace Libp2p.Core.Mock.Streams

/-- Placeholder for `Streams.Connection`. -/
opaque Connection : Type

/-- Placeholder for the close projection. The no-op body supplies
compiler code; it models no transport behavior. -/
opaque Connection.close (_conn : Connection) : IO Unit := pure ()

/-- Placeholder for `Streams.Stream`. -/
opaque Stream : Type

end Libp2p.Core.Mock.Streams
