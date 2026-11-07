import GossipsubInterop

/-! Host-free regression checks. Run these against the integrated tree. -/
set_option autoImplicit false

namespace Tests.Gossipsub.InteropDriver

open Libp2p.Protocols.Gossipsub.Interop

example : DelayTable.batchDelay [("a", 5), ("b", 12)] ["a", "b"] = 12 := by decide
example : DelayTable.batchDelay [("a", 5)] [] = 0 := by decide
example : DelayTable.batchDelay [("a", 5)] ["missing"] = 0 := by decide
example : (publishPayload 42 8).map ByteArray.size = .ok 8 := by decide
example : (publishPayload 43 98304).map ByteArray.size = .ok 98304 := by decide
example : (publishPayload 42 7).isError = true := by decide
example : (publishPayload 42 maxPayloadBytes).map ByteArray.size = .ok maxPayloadBytes.toNat := by decide
example : (publishPayload 42 (maxPayloadBytes + 1)).isError = true := by decide

example : nodeId? "node0" = some 0 := by decide
example : nodeId? "node31" = some 31 := by decide
example : nodeId? "node" = none := by decide
example : nodeId? "nodeX" = none := by decide
example : nodeId? "node-1" = none := by decide

/-- Compare against the independent Python vectors in GATE-TCP-PROBE. -/
def checkIdentityVectors : IO Unit := do
  let ids := [
    "12D3KooWDpJ7As7BWAwRMfu1VU2WCqNjvq387JEYKDBj4kx6nXTN",
    "12D3KooWPjceQrSwdWXPyLLeABRXmuqt69Rg3sBYbU1Nft9HyQ6X",
    "12D3KooWH3uVF6wv47WnArKHk5p6cvgCJEb74UTmxztmQDc298L3",
    "12D3KooWQYhTNQdmr3ArTeUHRYzFg94BKyTkoWBDWez9kSCVe2Xo"]
  for (node, expected) in ids.zipIdx |>.map (fun (id, n) => (n, id)) do
    let seed := peerSeed node
    unless seed == node :: List.replicate 31 0 do
      throw (IO.userError s!"node{node}: seed mismatch")
    match identityForNode node with
    | .error e => throw (IO.userError e)
    | .ok (_, peer) =>
      unless peer.toString == expected do
        throw (IO.userError s!"node{node}: peer id mismatch")

end Tests.Gossipsub.InteropDriver
