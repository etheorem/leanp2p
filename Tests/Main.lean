import Tests.Support
import Tests.Varint
import Tests.Multibase
import Tests.Multihash
import Tests.Multiaddr
import Tests.MultiaddrOps
import Tests.Multiselect
import Tests.Hashes
import Tests.Protobuf
import Tests.Keys
import Tests.Noise
import Tests.TlsExt
import Tests.Yamux
import Tests.Mplex
import Tests.PingId
import Tests.Envelope
import Tests.Fixtures
import Tests.Tcp
import Tests.Node
import Tests.Interop
import Tests.Spike

/-!
# Test entry point (VECTOR_TEST_PLAN.md, phase 0 step 3)

One module per suite, each naming the upstream file it mirrors. Run with
`lake test`; the exit code is nonzero only on real failures - documented
gaps ("todo") and not-yet-implemented vectors ("skipped") stay visible in
the summary without blocking CI.

The concurrency-sensitive suites (Tcp, Node) also pass under a single
capability: `lake test -- +RTS -N1 -RTS`.
-/

open Tests

def main : IO UInt32 := do
  let r ← Runner.new
  Varint.run r
  Multibase.run r
  Multihash.run r
  Multiaddr.run r
  MultiaddrOps.run r
  MultiselectSuite.run r
  YamuxSuite.run r
  MplexSuite.run r
  PingIdSuite.run r
  EnvelopeSuite.run r
  Hashes.run r
  Protobuf.run r
  Keys.run r
  NoiseSuite.run r
  TlsExtSuite.run r
  Fixtures.run r
  TcpSuite.run r
  NodeSuite.run r
  InteropSuite.run r
  Spike.run r
  r.summary
