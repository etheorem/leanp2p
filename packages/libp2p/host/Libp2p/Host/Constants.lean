/-!
# The constants of `libp2p/host`

Each fact has one home (ARCHITECTURE §3.8; PRINCIPLES 1.5). This module
holds the constants the host owns. The deadline of an unauthenticated
phase is not here: `net/streams` owns it (`Streams.unauthDeadlineMs`,
§5.4), and the upgrader applies it.
-/

set_option autoImplicit false

namespace Libp2p.Host

/-- The race window of the simultaneous-dial rule, in milliseconds
(§4.9; the package ARCHITECTURE, contract 2). Two connections to one
peer that run in opposite directions race when the standing session
was born less than this long before the new one. Inside the window,
the connection that the larger peer id dialed loses. Outside it, the
standing session keeps its place. Each side measures with its own
`Clock`. -/
def simulWindowMs : Nat := 30000

/-- The deadline of the multistream-select exchange on one muxed stream,
in milliseconds, in both roles. A peer that opens a stream and stays
silent, or that never answers our proposal, meets it, and the expiry
resets the stream. go-libp2p takes the same 10 s
(`DefaultNegotiationTimeout`,
`vendor/go-libp2p/p2p/host/basic/basic_host.go`, line 39). It sets
the deadline on an inbound stream before the negotiation (line 327),
and on `NewStream` when the caller gives none (lines 443 to 447). -/
def streamNegotiationMs : Nat := 10000

end Libp2p.Host
