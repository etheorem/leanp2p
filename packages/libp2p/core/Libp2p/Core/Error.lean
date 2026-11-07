/-!
# The coarse seam error

Every seam of this package fails with `Core.Error` (ARCHITECTURE §3.5,
§4.9). The arms name what the upgrader and the host do about a
failure, and each arm carries the error of the implementation as
rendered text for the log:

* `protocol`: the peer broke the spec. The connection closes.
* `authentication`: the peer did not prove the identity it claims, or
  it proved a different one.
* `timeout`: a deadline expired (§5.4).
* `closed`: the session or the connection ended before the operation
  could finish.

Each implementation owns its fine error type (`Noise.Error`,
`Yamux.ProtocolError`) and maps it into this type once, at its seam
value, with `Except.mapError` (owned contract 6). The upgrader and the
host match on this one type, so core imports no implementation's
error. The rendered text keeps the detail that the arm drops.
-/

set_option autoImplicit false

namespace Libp2p.Core

/-- A seam failure: the kind the caller acts on, and the rendered
error of the implementation. -/
inductive Error where
  /-- The peer, or our own input, broke the spec. -/
  | protocol (detail : String)
  /-- The peer failed to authenticate, or it authenticated as an
  unexpected peer id. -/
  | authentication (detail : String)
  /-- A deadline expired before the operation finished. -/
  | timeout (detail : String)
  /-- The session or the connection ended under the operation. -/
  | closed (detail : String)
  deriving DecidableEq, Repr, Hashable

namespace Error

/-- The log line of the error: the kind, then the rendered detail of
the implementation. -/
def render : Error → String
  | .protocol d => s!"protocol error: {d}"
  | .authentication d => s!"authentication failure: {d}"
  | .timeout d => s!"timeout: {d}"
  | .closed d => s!"closed: {d}"

instance : ToString Error := ⟨render⟩

end Error

end Libp2p.Core
