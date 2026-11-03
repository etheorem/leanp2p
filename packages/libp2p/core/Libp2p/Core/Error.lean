/-!
# Errors at libp2p interfaces

Implementations map their protocol errors to `Core.Error` at the seam,
using `Except.mapError` or `ExceptT.adapt`. Each variant retains the
rendered detail for logging. System faults remain thrown `IO.Error`s
(ARCHITECTURE §3.5, §4.9).
-/

set_option autoImplicit false

namespace Libp2p.Core

/-- A libp2p failure with the rendered implementation error as detail. -/
inductive Error where
  /-- The peer, or our own input, broke a spec. -/
  | protocol (detail : String)
  /-- The peer failed to authenticate, or authenticated as a peer we
  did not expect. -/
  | authentication (detail : String)
  /-- A deadline expired before the operation finished (§5.4). -/
  | timeout (detail : String)
  /-- The connection or the session ended before the operation
  finished. -/
  | closed (detail : String)
  deriving DecidableEq, Repr, Hashable

namespace Error

/-- The rendered error of the implementation that the arm carries. -/
def detail : Error → String
  | .protocol d => d
  | .authentication d => d
  | .timeout d => d
  | .closed d => d

/-- The log line of an error: the arm, then the detail. -/
def render : Error → String
  | .protocol d => s!"protocol error: {d}"
  | .authentication d => s!"authentication failed: {d}"
  | .timeout d => s!"timeout: {d}"
  | .closed d => s!"closed: {d}"

/-- Render the error for logging. -/
instance : ToString Error := ⟨render⟩

/-- Render an implementation error as a protocol failure.
Usage: `(step s ev).mapError Core.Error.ofProtocol`. -/
def ofProtocol {ε : Type} [ToString ε] (e : ε) : Error :=
  .protocol (ToString.toString e)

/-- `ofProtocol` keeps the rendered inner error as the detail. -/
theorem detail_ofProtocol {ε : Type} [ToString ε] (e : ε) :
    (ofProtocol e).detail = ToString.toString e := rfl

end Error

end Libp2p.Core
