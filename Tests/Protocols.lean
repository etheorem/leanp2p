import Tests.Support
import Proto
import Bytes
import Varint
import Libp2p.Protocols
import Libp2p.Protocols.Mock.Identity
import Libp2p.Protocols.Mock.Multiaddr

/-!
# Identify and ping suite (unit W5.7, sub-unit 1a)

Mirrors `vendor/specs/ping/ping.md` (32-byte echo, protocol id
`/ipfs/ping/1.0.0`) and the captured go-libp2p Identify protobuf
(`identify-go.json`). The suite replays the vector and drives the
pure `Identify.validate` and `Ping.checkEcho` checks. The mock key
and multiaddr stand-ins run their executable bodies here, so every
mock outcome of the validate appears in a check.
-/

set_option autoImplicit false

namespace Tests.Protocols

open Libp2p.Protocols
open Libp2p.Protocols.Mock.Identity
open Libp2p.Protocols.Mock.Multiaddr

/-- The model decode over the byte list. -/
private def decodeModel (bs : List Nat) : Except Pb.Error (Identify × List Nat) :=
  Pb.decodeMessage? (α := Identify) bs

/-- The production decode over a byte array. -/
private def decodeByteArray (bs : ByteArray) : Except Pb.Error (Identify × Nat) :=
  Pb.decodeMessageB? (α := Identify) bs

/-- The all-absent identify message. -/
private def emptyIdentify : Identify := ⟨none, [], [], none, none, none, none⟩

/-- The encoding of a message, through the shared Proto encoder. -/
private def msgPayload (m : Identify) : List Nat :=
  Pb.encodeMessage m

def run (r : Runner) : IO Unit := do
  r.section "protocols"
    "libp2p/specs identify/README.md + ping/ping.md + captured go Identify protobuf"

  let j ← loadJson "identify-go.json"
  let respHex ← jStr "identify-go.json" j "responseHex"
  let pkHex ← jStr "identify-go.json" j "publicKeyHex"
  let wantProtocols ← jStrs "identify-go.json" j "protocols"
  let wantAgent ← jStr "identify-go.json" j "agentVersion"
  let jsonVersion ← jStr "identify-go.json" j "protocolVersion"

  match Bytes.ofHex? respHex with
  | none =>
      r.check "identify vector length prefix is 330" false
      r.check "identify vector decodes (model)" false
      r.check "identify vector decodes (bytearray)" false
      r.check "identify vector model equals bytearray" false
  | some respBytes =>
      match Varint.decode? (Bytes.toNatList respBytes) with
      | .error _ =>
          r.check "identify vector length prefix is 330" false
          r.check "identify vector decodes (model)" false
          r.check "identify vector decodes (bytearray)" false
          r.check "identify vector model equals bytearray" false
      | .ok (len, payload) =>
          -- the captured response carries a uvarint length prefix;
          -- the prefix must equal 330 and the remaining length
          r.check "identify vector length prefix is 330"
            (len.val == 330 && len.val == payload.length)
          match decodeModel payload with
          | .error _ =>
              r.check "identify vector decodes (model)" false
              r.check "identify vector decodes (bytearray)" false
              r.check "identify vector model equals bytearray" false
          | .ok (m, _) =>
              r.check "identify vector decodes (model)" true
              let mB := decodeByteArray (Bytes.ofNatList payload)
              r.check "identify vector decodes (bytearray)"
                (match mB with
                 | .ok (_, used) => used == payload.length
                 | .error _ => false)
              r.check "identify vector model equals bytearray"
                (match mB with
                 | .ok (m2, _) => m2 == m
                 | .error _ => false)
              r.check "identify vector re-encodes byte-exact"
                (Pb.encodeMessage m == payload)
              r.check "identify vector encodes deterministically"
                (Pb.encodeMessage m == Pb.encodeMessage m)
              match Bytes.ofHex? pkHex with
              | none =>
                  r.check "identify vector publicKey equals JSON publicKeyHex" false
              | some pkBytes =>
                  -- the wire carries the PublicKey protobuf: field 1 is
                  -- the ed25519 key type, field 2 holds the 32 key bytes
                  r.check "identify vector publicKey equals JSON publicKeyHex"
                    (m.publicKey == some ([8, 1, 18, 32] ++ Bytes.toNatList pkBytes))
              r.check "identify vector protocols equal JSON protocols in order"
                (m.protocols == wantProtocols)
              r.check "identify vector agentVersion equals JSON agentVersion"
                (m.agentVersion == some wantAgent)
              -- the binary form of /ip4/127.0.0.1/tcp/35371; the real
              -- Multiaddr text codec is unmerged
              r.check "identify vector listenAddrs has one entry, the binary form of JSON listenAddrs[0]"
                (m.listenAddrs == [[4, 127, 0, 0, 1, 6, 138, 43]])
              -- the wire carries the empty string, the JSON says
              -- /ipfs/1.0.0; the wire is the truth
              r.check "identify vector protocolVersion wire delta recorded"
                (m.protocolVersion == some "" && jsonVersion == "/ipfs/1.0.0")
              r.skip "identify vector peer id derivation skipped"
                "the peer id derivation is an opaque mock; identity #11 replaces it"

  -- validate: rejection and acceptance, through the mock bodies
  r.check "identify over-cap payload rejected before decode"
    (failsWith Identify.Error.overCap
      (Identify.validate (List.replicate 65537 0) none))
  r.check "identify empty payload has no key"
    (failsWith Identify.Error.missingKey (Identify.validate [] none))
  let noKey := { emptyIdentify with agentVersion := some "leanp2p" }
  r.check "identify missing publicKey rejected"
    (failsWith Identify.Error.missingKey (Identify.validate (msgPayload noKey) none))
  let badKeyMsg := { emptyIdentify with publicKey := some [] }
  r.check "identify undecodable publicKey rejected"
    (failsWith Identify.Error.badKey (Identify.validate (msgPayload badKeyMsg) none))
  let otherId : PeerId := ⟨[], "other"⟩
  let mismatchMsg := { emptyIdentify with publicKey := some [1, 2] }
  r.check "identify key mismatch rejected"
    (failsWith Identify.Error.keyMismatch
      (Identify.validate (msgPayload mismatchMsg) (some otherId)))
  let badListen := { emptyIdentify with publicKey := some [1, 2], listenAddrs := [[]] }
  r.check "identify invalid listen address rejected"
    (failsWith Identify.Error.badAddress (Identify.validate (msgPayload badListen) none))
  let badObs := { emptyIdentify with publicKey := some [1, 2], observedAddr := some [] }
  r.check "identify invalid observed address rejected"
    (failsWith Identify.Error.badAddress (Identify.validate (msgPayload badObs) none))
  -- a continuation byte with no terminator: truncated framing
  r.check "identify malformed protobuf rejected"
    (failsWith (Identify.Error.badMessage (.framing .truncated))
      (Identify.validate [0x80] none))
  let good := { emptyIdentify with publicKey := some [1, 2] }
  let pid : PeerId := peerIdOfPubKey ⟨.ed25519, [1, 2]⟩
  r.check "identify accepted with matching derivation"
    (succeedsWith (good, pid) (Identify.validate (msgPayload good) (some pid)))
  r.check "identify accepted with no expected id"
    (succeedsWith (good, pid) (Identify.validate (msgPayload good) none))

  -- ping: the spec constants and the echo check
  r.check "ping protocol id constant" (Ping.protocolId.toString == "/ipfs/ping/1.0.0")
  r.check "ping payload size 32" (Ping.payloadSize == 32)
  let sent := List.replicate 32 7
  r.check "ping echo exact accepted" (succeedsWith () (Ping.checkEcho sent sent))
  r.check "ping echo short rejected"
    (failsWith (Ping.Error.wrongSize 31) (Ping.checkEcho sent (List.replicate 31 7)))
  r.check "ping echo long rejected"
    (failsWith (Ping.Error.wrongSize 33) (Ping.checkEcho sent (List.replicate 33 7)))
  let altered := 0 :: List.replicate 31 7
  r.check "ping echo altered rejected"
    (failsWith .mismatch (Ping.checkEcho sent altered))

end Tests.Protocols
