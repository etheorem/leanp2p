import Libp2p.Protocols.Mock.Core

/-!
# Protocol constants

One home per literal (DRY). The module holds the protocol ids of
identify, identify push, and ping, the identify message cap, and the
ping payload size. Gossipsub and req/resp ids wait for their units.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Constants

/-- The identify protocol id, `/ipfs/id/1.0.0`. -/
def identifyId : Mock.Core.ProtocolId := ⟨"/ipfs/id/1.0.0"⟩

/-- The identify push protocol id, `/ipfs/id/push/1.0.0`. -/
def identifyPushId : Mock.Core.ProtocolId := ⟨"/ipfs/id/push/1.0.0"⟩

/-- The ping protocol id, `/ipfs/ping/1.0.0`. -/
def pingId : Mock.Core.ProtocolId := ⟨"/ipfs/ping/1.0.0"⟩

/-- The identify message cap, inherited from the spike: 65536 bytes. -/
def identifyCap : Nat := 65536

/-- The ping payload size of the spec: 32 bytes. -/
def pingSize : Nat := 32

/-- The protocol version the responder writes, the spike's constant. -/
def identifyProtocolVersion : String := "/ipfs/1.0.0"

end Libp2p.Protocols.Constants
