import Bytes
import Yamux.Constants

/-!
# Yamux protocol errors

One inductive for every way a peer can break the specification on the
wire (ARCHITECTURE §3.5). The package maps it into the coarse error of
the protocol stack once, at the seam value, and the session reports it
to its owner through its completion.

A short input is not an error. `Frame.parse?` answers `none` for it and
the reader waits for more bytes.
-/

set_option autoImplicit false


namespace Yamux

/-- Why the session tore the connection down. -/
inductive ProtocolError where
  /-- The twelve header bytes violate the header codec. -/
  | header
  /-- A data frame declared more bytes than the receive window grants. -/
  | overlongData
  /-- A window update would push the send window past its field. -/
  | windowOverflow
  /-- A frame arrived after the peer ended the session. -/
  | sessionClosed
  /-- A frame names a stream that neither side opened. -/
  | unknownStream
  /-- This side has used every stream id of its parity. -/
  | exhausted
  /-- The peer opened more streams than the backlog cap allows. -/
  | backlog
  deriving Repr, DecidableEq, BEq, Hashable

end Yamux
