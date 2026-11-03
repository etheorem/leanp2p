/-!
# Identity mock

Temporary `PeerId` interface for W5.1 (#11). This module imports no
real identity implementation and adds no dependency axioms.
See `docs/ARCHITECTURE.md`, "The mocks", for integration steps.
-/

set_option autoImplicit false

namespace Libp2p.Core.Mock.Identity

/-- Placeholder for `Libp2p.Identity.PeerId`. -/
opaque PeerId : Type

end Libp2p.Core.Mock.Identity
