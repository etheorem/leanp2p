/-!
# Multiaddr mock

Temporary address type while W2.3 and W4.1 are pending. Core will
obtain `Multiaddr` through streams. This module adds no dependency
axioms. See `docs/ARCHITECTURE.md`, "The mocks", for integration steps.
-/

set_option autoImplicit false

namespace Libp2p.Core.Mock.Multiformats

/-- Placeholder for `Multiformats.Multiaddr`. -/
opaque Multiaddr : Type

end Libp2p.Core.Mock.Multiformats
