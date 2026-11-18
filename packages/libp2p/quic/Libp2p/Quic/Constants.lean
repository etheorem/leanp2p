/-!
# The constants of `libp2p/quic`

Each fact has one home (root ARCHITECTURE §3.8; PRINCIPLES 1.5). The
numbers of the QUIC engine live in `net/quic` (`Quic/Constants.lean`);
this module holds the ones the libp2p value adds.
-/

set_option autoImplicit false

namespace Libp2p.Quic

/-- The application error code of a connection that the value refuses
after its handshake: 0x1003, go-libp2p's `ConnProtocolViolation`
(`vendor/go-libp2p/core/network/conn.go`). The value refuses when the
handshake's result contradicts the checks that ran inside it, on the
ALPN or the peer. The engine's checks make that case a fault, so the
code marks a refusal that should not occur. -/
def protocolViolation : UInt64 := 0x1003

end Libp2p.Quic
