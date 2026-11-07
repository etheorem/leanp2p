import Conc
import Libp2p.Protocols.Gossipsub.Interop
import GossipsubInterop
import GossipsubSession

/-! The socket participant executable. -/
set_option autoImplicit false

namespace Cli

open Conc Streams Multiformats Libp2p.Core Libp2p.Identity Libp2p.Host
open Libp2p.Protocols Libp2p.Protocols.Constants
open Libp2p.Protocols.Gossipsub Libp2p.Protocols.Gossipsub.Node
open Libp2p.Protocols.Gossipsub.Interop

private def fail (message : String) : IO UInt32 := do
  IO.eprintln message
  return 1

def load (path : System.FilePath) (nodeId : Nat) : IO (Except String (GossipSubParams × List Instruction)) := do
  let source ← IO.FS.readFile path
  return (parseScript source).bind (prepareScript (Int.ofNat nodeId))

def run (args : List String) : IO UInt32 := do
  let start ← Conc.Clock.system.nowMs
  let path ← match paramsPath args with
    | .ok value => pure value
    | .error e => return ← fail e
  let hostName ← try
    processHostname
  catch e =>
    return ← fail (toString e)
  let some nodeId := nodeId? hostName | return ← fail s!"invalid node hostname: {hostName}"
  let script ← match ← load path nodeId with
    | .ok value => pure value
    | .error e => return ← fail e
  let (params, actions) := script
  let (identity, peer) ← match identityForNode nodeId with
    | .ok value => pure value
    | .error e => return ← fail e
  let writer ← BaseIO.toIO RecordWriter.start
  let observer ← BaseIO.toIO (ReceiptObserver.new writer)
  let coreParams ← match toCoreParams params with
    | .ok value => pure value
    | .error e => return ← fail e
  let receiptCallback : Peer → List Nat → BaseIO Unit := fun sender bytes =>
    observer.onRpc (toString sender) bytes
  let config : Node.Config := { params := coreParams, onRpc := receiptCallback }
  let running ← match ← GossipsubSession.start identity config with
    | .ok value => pure value
    | .error e => return ← fail e
  let listenAddr ← match Multiaddr.parse? "/ip4/0.0.0.0/tcp/9000" with
    | .ok value => pure value
    | .error e => return ← fail (reprStr e)
  let listenResult ← (running.host.startListening listenAddr).run
  match listenResult with
  | .error e => return ← fail (reprStr e)
  | .ok _ => pure ()
  let peerTime ← BaseIO.toIO observationTime
  let peerLine ← BaseIO.toIO (RecordWriter.offer writer (peerRecord peerTime peer.toString nodeId))
  if !peerLine then return ← fail "PeerID record queue full or closed"
  let driver : Driver := {
    connect := fun target => do
      if target < 0 then return .error "connectTo must be nonnegative"
      let (_, targetPeer) ← match identityForNode target.toNat with
        | .ok value => pure value
        | .error e => return .error e
      let addressText := s!"/ip4/172.30.246.{10 + target.toNat}/tcp/9000"
      let address ← match Multiaddr.parse? addressText with
        | .ok value => pure value
        | .error e => return .error (reprStr e)
      running.host.addAddrs targetPeer [address]
      match ← running.host.dialPeer targetPeer with
        | .ok joined =>
          if ← running.node.peerJoined joined .meshsub then pure (.ok ())
          else pure (.error "peerJoined queue refused")
        | .error e => pure (.error (reprStr e))
    subscribe := fun topic _ => running.node.subscribe ⟨topic⟩ (fun _ => pure ())
    publish := fun topic payload => running.node.publish ⟨topic⟩ payload
    validationDelay := fun _ _ => pure () }
  let resultCode ← try
    match ← (runScript driver Conc.Clock.system start actions).run with
    | .ok () => pure 0
    | .error e => IO.eprintln e; pure 1
  catch e =>
    IO.eprintln (toString e)
    pure 1
  let stopCode ← try
    (GossipsubSession.stop running).run
    pure 0
  catch e =>
    IO.eprintln (toString e)
    pure 1
  let closeCode ← try
    (RecordWriter.close writer).run
    pure 0
  catch e =>
    IO.eprintln (toString e)
    pure 1
  let failures ← BaseIO.toIO observer.failureCount
  return if resultCode = 0 && stopCode = 0 && closeCode = 0 && failures = 0 then 0 else 1

end Cli

def main (args : List String) : IO UInt32 := Cli.run args
