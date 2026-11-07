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
  let delayTable ← BaseIO.toIO DelayTable.new
  let traceEnabled := (← IO.getEnv "INTEROP_TRACE").getD "" == "1"
  let coreParams ← match toCoreParams params with
    | .ok value => pure value
    | .error e =>
      (RecordWriter.close writer).run
      return ← fail e
  let receiptCallback : Peer → List Nat → BaseIO Unit := fun sender bytes => do
    traceInbound traceEnabled (toString sender) bytes
    observer.onRpc (toString sender) bytes
  let sendCallback : Peer → Rpc.RPC → BaseIO Unit := fun peer rpc =>
    traceOutbound traceEnabled peer rpc
  let config : Node.Config := { params := coreParams, onRpc := receiptCallback, onSend := sendCallback }
  let mut running : Option GossipsubSession.Running := none
  let mut resultCode : UInt32 := 1
  try
    let started ← GossipsubSession.start identity config
    let active ← match started with
      | .ok value => pure value
      | .error e => throw (IO.userError e)
    running := some active
    let listenAddr ← match Multiaddr.parse? "/ip4/0.0.0.0/tcp/9000" with
      | .ok value => pure value
      | .error e => throw (IO.userError (reprStr e))
    match ← (active.host.startListening listenAddr).run with
    | .error e => throw (IO.userError (reprStr e))
    | .ok _ => pure ()
    let peerTime ← BaseIO.toIO observationTime
    let peerLine ← BaseIO.toIO (RecordWriter.offer writer (peerRecord peerTime peer.toString nodeId))
    unless peerLine do throw (IO.userError "PeerID record queue full or closed")
    let driver : Driver := {
      connect := fun target => do
        if target < 0 then return .error "connectTo must be nonnegative"
        let (_, targetPeer) ← match identityForNode target.toNat with
          | .ok value => pure value
          | .error e => return .error e
        let nodeName := s!"node{target.toNat}"
        let ip? ← lookupHostsFile nodeName
        let addressText ← match ip? with
          | none => return .error s!"no /etc/hosts entry for {nodeName}"
          | some ip =>
            match multiaddrPrefix ip with
            | some value => pure value
            | none => return .error s!"invalid IPv4 entry for {nodeName}"
        let address ← match Multiaddr.parse? addressText with
          | .ok value => pure value
          | .error e => return .error (reprStr e)
        active.host.addAddrs targetPeer [address]
        let mut dialResult := ← active.host.dialPeer targetPeer
        for attempt in [1, 2, 3, 4] do
          match dialResult with
          | .error (.unreachable _) =>
            IO.eprintln s!"dial {nodeName} unreachable, retry {attempt}/5 after 200 ms"
            let timer ← (Conc.Clock.system.after 200 : BaseIO (Conc.Park Unit))
            discard <| Conc.select #[timer]
            dialResult ← active.host.dialPeer targetPeer
          | _ => break
        match dialResult with
          | .ok joined =>
            if ← active.node.peerJoined joined .meshsub then pure (.ok ())
            else pure (.error "peerJoined queue refused")
          | .error e => pure (.error (reprStr e))
      subscribe := fun topic _ => active.node.subscribe ⟨topic⟩ (fun _ => pure ())
      publish := fun topic payload => active.node.publish ⟨topic⟩ payload
      validationDelay := fun topic delay => delayTable.set topic delay }
    match ← (runScript driver Conc.Clock.system start actions).run with
    | .ok () => resultCode := 0
    | .error e => IO.eprintln e
  catch e =>
    IO.eprintln (toString e)
  let stopCode ← match running with
    | none => pure 0
    | some active => try
        (GossipsubSession.stop active).run
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
