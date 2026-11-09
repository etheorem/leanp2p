import Libp2p.Core.ProtocolId
import Libp2p.Protocols.Mock.Core

/-!
# Protocol constants

One home per literal (ARCHITECTURE §3.8, PRINCIPLES 1.5). Each section
holds the ids and the caps of one protocol of the package: identify,
identify push, and ping first, then req/resp and the snappy framing
format.

## Identify and ping

The identify values follow go-libp2p's identify service, and the ping
values follow its ping service. Each docstring names its source.

## Req/resp

The values come from the consensus networking spec,
`vendor/consensus-specs/specs/phase0/p2p-interface.md` and
`vendor/consensus-specs/specs/altair/p2p-interface.md`, and from the
snappy framing format, `vendor/snappy/framing_format.txt`. Each
docstring names its section.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Constants

/-- The gossipsub v1.1 protocol id, `/meshsub/1.1.0`. -/
def meshsubId : Libp2p.Core.ProtocolId := ⟨"/meshsub/1.1.0"⟩

/-- The gossipsub v1.0 protocol id, `/meshsub/1.0.0`. A v1.1 router speaks v1.0 to a peer that
offers only this id. -/
def meshsubV10Id : Libp2p.Core.ProtocolId := ⟨"/meshsub/1.0.0"⟩

/-- The floodsub protocol id, `/floodsub/1.0.0`. -/
def floodsubId : Libp2p.Core.ProtocolId := ⟨"/floodsub/1.0.0"⟩

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

-- Req/resp takes its ids from `libp2p/core`. The identify and ping ids
-- above stay on the mock until their swap (issue #55).
open Libp2p.Core (ProtocolId)

/-! ## Req/resp: the protocol id -/

/-- The prefix of every req/resp protocol id, "Protocol identification"
of the phase0 spec. -/
def reqRespPrefix : String := "/eth2/beacon_chain/req"

/-- The one encoding the spec defines, "Encoding strategies". -/
def sszSnappy : String := "ssz_snappy"

/-- The id of one req/resp method:
`/ProtocolPrefix/MessageName/SchemaVersion/Encoding`. The spec limits
`name` to English letters, digits, and `_`, and `version` is an
ordinal. The client project names its methods, so the names stay out of
this package. -/
def reqRespId (name : String) (version : Nat) : ProtocolId :=
  ⟨reqRespPrefix ++ "/" ++ name ++ "/" ++ toString version ++ "/" ++ sszSnappy⟩

/-! ## Req/resp: the size caps -/

/-- `MAX_PAYLOAD_SIZE`, 10 MiB: the cap on the uncompressed payload of
one chunk, phase0 "Configs". -/
def maxPayloadSize : Nat := 10 * 2 ^ 20

/-- `max_compressed_len(n)`, phase0 "Maximum message sizes": the most
framed bytes a reader takes after the length prefix `n`. -/
def maxCompressedLen (n : Nat) : Nat := 32 + n + n / 6

/-- The length prefix is a protobuf varint of at most 10 bytes, "SSZ-snappy
encoding strategy". -/
def lengthPrefixMaxBytes : Nat := 10

/-- The width of the `ForkDigest` context, altair "Req-Resp interaction". -/
def forkDigestLen : Nat := 4

/-- `ErrorMessage.LIMIT`: the payload of an error chunk is at most 256
bytes, phase0 "Types". -/
def errorMessageLimit : Nat := 256

/-- `MAX_CONCURRENT_REQUESTS`: the most requests a requester has open
with one protocol id, phase0 "Configs" and "Requesting side". -/
def maxConcurrentRequests : Nat := 2

/-! ## Req/resp: the result codes

The `result` byte of a response chunk, phase0 "Responding side". -/

/-- `Success`. -/
def resultSuccess : Nat := 0
/-- `InvalidRequest`. -/
def resultInvalidRequest : Nat := 1
/-- `ServerError`. -/
def resultServerError : Nat := 2
/-- `ResourceUnavailable`. The reserved range `[4, 127]` and the
request-specific range `[128, 255]` are arms of `ReqResp.Result`. -/
def resultResourceUnavailable : Nat := 3

/-! ## The snappy framing format

`framing_format.txt` of google/snappy, sections 1 to 4. -/

/-- A chunk header: one type byte and a 3-byte little-endian length. -/
def snappyHeaderLen : Nat := 4

/-- The largest length the 3-byte field holds, `2 ^ 24 - 1`. -/
def snappyMaxChunkLen : Nat := 2 ^ 24 - 1

/-- The masked CRC-32C that opens a data chunk is 4 bytes. -/
def snappyCrcLen : Nat := 4

/-- The most uncompressed bytes one data chunk carries, sections 4.2
and 4.3. -/
def snappyMaxDataLen : Nat := 65536

/-- The body of the stream identifier chunk, `sNaPpY` in ASCII,
section 4.1. -/
def snappyStreamBody : List Nat := [0x73, 0x4e, 0x61, 0x50, 0x70, 0x59]

/-- The constant the checksum mask adds, section 3. -/
def snappyMaskDelta : Nat := 0xa282ead8

/-- The chunk type of the stream identifier, section 4.1. -/
def snappyStreamId : Nat := 0xff
/-- The chunk type of compressed data, section 4.2. -/
def snappyCompressed : Nat := 0x00
/-- The chunk type of uncompressed data, section 4.3. -/
def snappyUncompressed : Nat := 0x01
/-- The chunk type of padding, section 4.4. The two reserved ranges,
`0x02` to `0x7f` and `0x80` to `0xfd`, are arms of `SnappyFrame.Kind`. -/
def snappyPadding : Nat := 0xfe

end Libp2p.Protocols.Constants
