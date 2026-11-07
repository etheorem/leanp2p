import Libp2p.Protocols.Mock.Core

/-!
# Protocol constants

The gossipsub protocol ids and the RPC cap. Identify and req/resp add
their own constants with their own units.
Other modules read these values from this module and do not repeat the
literals. The module holds the protocol ids of
identify, identify push, and ping, the identify message cap, the
identify protocol version, and the ping payload size.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Constants

/-- The gossipsub v1.1 protocol id, `/meshsub/1.1.0`. -/
def meshsubId : Mock.Core.ProtocolId := ⟨"/meshsub/1.1.0"⟩

/-- The gossipsub v1.0 protocol id, `/meshsub/1.0.0`. A v1.1 router
speaks v1.0 to a peer that offers only this id. -/
def meshsubV10Id : Mock.Core.ProtocolId := ⟨"/meshsub/1.0.0"⟩

/-- The floodsub protocol id, `/floodsub/1.0.0`. -/
def floodsubId : Mock.Core.ProtocolId := ⟨"/floodsub/1.0.0"⟩

/-- The gossipsub RPC cap: 1 MiB, the go-libp2p-pubsub default. -/
def rpcCap : Nat := 1048576
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