/-!
# The error of `net/streams`

The package owns one error inductive (ARCHITECTURE §3.5). It names why a
`Stream` operation did not complete. A framing read reports through the
shared `DecodeError` of `base/bytes` instead, since a length prefix is
a codec answer (§3.2). A connection fault stays an `IO.Error`.
-/

set_option autoImplicit false

namespace Streams

/-- Why a stream operation did not complete. -/
inductive Error where
  /-- The stream, or the session that serves it, closed before the
  operation completed. -/
  | closed
  /-- The stream was reset. A reset stops both directions, so the bytes
  in flight can be lost (§5.3). -/
  | reset
  /-- The peer did not answer in time, as a muxer ping that no pong
  answers within its deadline. -/
  | timeout
  deriving Repr, DecidableEq, BEq, Inhabited

end Streams
