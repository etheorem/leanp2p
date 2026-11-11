import Tests.Support
import Tests.Gossipsub.Core
import Tests.Gossipsub.Sign
import Tests.Gossipsub.Cache
import Tests.Gossipsub.Score
import Tests.Gossipsub.Rpc
import Tests.Gossipsub.Node
import Tests.Gossipsub.Wire
import Tests.Gossipsub.Interop
import Tests.Vectors
import Tests.Concurrency
import Tests.Protobuf
import Tests.Bytes
import Tests.Varint
import Tests.Snappy
import Tests.Multiformats
import Tests.MultiaddrWire
import Tests.Streams
import Tests.Mux
import Tests.Mplex
import Tests.Backend
import Tests.HazmatPins
import Tests.BackendX509
import Tests.BackendStrict
import Tests.BackendSoak
import Tests.Hashes
import Tests.Facade
import Tests.CryptoCross
import Tests.Yamux
import Tests.Identity
import Tests.Core
import Tests.Noise
import Tests.Rlp
import Tests.Enr
import Tests.Negotiate
import Tests.Upgrade
import Tests.Host
import Tests.Protocols
import Tests.ReqResp
import Tests.Interop
import Tests.Cli

/-!
# Test entry point

One module per suite, each naming the upstream file it mirrors.
`lake test` runs the driver; the exit code is nonzero only on real
failures. Documented gaps (todo) and skipped vectors stay visible in the
summary without failing the run. The concurrency-sensitive suites also
pass under a single capability: `lake test -- +RTS -N1 -RTS`
(ARCHITECTURE §6).
-/

def main : IO UInt32 := do
  let r ← Tests.Runner.new
  Tests.Vectors.run r
  Tests.Gossipsub.Core.run r
  Tests.Gossipsub.Sign.run r
  Tests.Gossipsub.Cache.run r
  Tests.Gossipsub.Score.run r
  Tests.Gossipsub.Rpc.run r
  Tests.Gossipsub.Node.run r
  Tests.Gossipsub.Wire.run r
  Tests.Gossipsub.Interop.run r
  Tests.Concurrency.run r
  Tests.Protobuf.run r
  Bytes.runTests r
  Tests.Varint.run r
  Tests.Snappy.run r
  Tests.Multiformats.run r
  Tests.MultiaddrWire.run r
  Tests.Streams.run r
  Tests.Mux.run r
  Tests.Mplex.run r
  Tests.Backend.run r
  Tests.HazmatPins.run r
  Tests.BackendX509.run r
  Tests.BackendStrict.run r
  Tests.BackendSoak.run r
  Tests.Hashes.run r
  Tests.Facade.run r
  Tests.CryptoCross.run r
  Tests.Yamux.run r
  Tests.Identity.run r
  Tests.Core.run r
  Tests.Noise.run r
  Tests.Rlp.run r
  Tests.Enr.run r
  Tests.Negotiate.run r
  Tests.Upgrade.run r
  Tests.Host.run r
  Tests.Protocols.run r
  Tests.ReqResp.run r
  Tests.Interop.run r
  Tests.Cli.run r
  r.summary
