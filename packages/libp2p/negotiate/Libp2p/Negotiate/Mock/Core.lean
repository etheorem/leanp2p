import Std

/-!
# Core mocks for unit 1a

`ProtocolId` and `Role` live in `libp2p/core` (W5.2, not merged yet).
This module holds them verbatim from the core ARCHITECTURE "Public
surface", so the negotiate core compiles against the frozen shapes.
The import swaps to `Libp2p.Core` when W5.2 lands. `Repr` joins the
derived classes per root §3.2, so `State`, `Event`, and `Action` can
derive `Repr` per root §3.3.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate.Mock.Core

/-- A wrapped-string protocol id. Peers define ids, so the set stays
open. Code compares `ProtocolId` values only (root §3.4). -/
structure ProtocolId where
  toString : String
  deriving DecidableEq, Hashable, Repr

/-- The role of one side of a negotiation (root §4.9). No spec gives
roles a wire code, so it has no `toCode`/`ofCode?` pair. -/
inductive Role where
  | initiator
  | responder
  deriving DecidableEq, Repr, Hashable

end Libp2p.Negotiate.Mock.Core
