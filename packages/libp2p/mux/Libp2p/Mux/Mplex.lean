import Libp2p.Core.Mux
import Libp2p.Mux.Constants
import Libp2p.Mux.Mplex.Session

/-!
# The mplex muxer

`Mux.mplex` is the `Muxer` for `/mplex/6.7.0`
(`vendor/specs/mplex/README.md`). `open` passes the connection and the
negotiation leftover to `Mplex.Session.start`. The role has no part in
mplex: both sides number their streams from zero, and the session keys
each stream by `(id, initiator)` (`Mplex/State.lean`). `ExceptT.lift`
returns the session on the seam, and the lift adds no error arm.

The codec lives in `Mplex/Wire.lean`, the stream table in
`Mplex/State.lean`, and the tasks in `Mplex/Session.lean`.
-/

set_option autoImplicit false

namespace Libp2p.Mux

open Libp2p.Core

/-- The mplex muxer. `id` is `mplexId`. `open` starts the session.
The leftover bytes are the reader's first input. -/
def mplex : Muxer where
  id := mplexId
  «open» := fun _ connection leftover =>
    ExceptT.lift (Mplex.Session.start connection leftover)

end Libp2p.Mux
