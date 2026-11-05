/-!
# Protocol ids

A protocol id names a protocol on the wire. multistream-select
proposes it, and the peer echoes it back or answers `na` (the
connections spec, "Protocol Negotiation"). The spec allows any
string: "While any string can be used, the conventional format is a
path-like structure", such as `/yamux/1.0.0`. Peers define new ids, so
no closed set can hold them (ARCHITECTURE §3.4). libp2p routes each id
to its handler "using exact literal matching", so equality of the text
is the whole comparison.

`ProtocolId` wraps the string, so code compares `ProtocolId` values
and never raw strings (§3.1, §3.4). The known ids are named constants
in one module per protocol package (`Mux.yamuxId`,
`Identify.protocolId`); this package owns the type and no constant of
it (owned contract 2).
-/

set_option autoImplicit false

namespace Libp2p.Core

/-- A protocol id: the exact text that multistream-select carries.

The derived classes are the standard ones of §3.2. `DecidableEq` and
`Hashable` serve the handler registry of the host
(`Std.HashMap ProtocolId StreamHandler`, §3.10). `Ord` orders by the
text, so a sorted `ls` answer is deterministic. -/
structure ProtocolId where
  /-- The id text, exactly as it travels on the wire. -/
  toString : String
  deriving DecidableEq, Hashable, Ord, Repr

/-- The id prints as its wire text. The derived `Repr` keeps the
structure form for test output. -/
instance : ToString ProtocolId := ⟨ProtocolId.toString⟩

end Libp2p.Core
