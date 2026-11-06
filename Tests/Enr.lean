import Tests.Support
import Tests.Backend
import Libp2p.Identity

/-!
# ENR suite (unit W6.1)

The checks of `packages/libp2p/identity/docs/PLAN.md`, unit 2: the
EIP-778 example record (`enr-eip778.json`, from
`vendor/eips/EIPS/eip-778.md`), one rejection per decode rule, the
signer, the text form, and the peer-id and multiaddr mapping.

The record verifies through the `Crypto` facade. A wrong digest or a
wrong recovery fails its signature and its node id, so the record pins
the whole path. The signer re-signs the example from its private key
to the record's own bytes. The text form reads and prints the
example's text, and it refuses each case of `enr-text-sigp.json`.

The peer id of the example key comes from go-libp2p at the vendored
commit (`3c2c902`), `peer.IDFromPublicKey` over
`crypto.UnmarshalSecp256k1PublicKey`. The PR test plan records the
program.
-/

set_option autoImplicit false

namespace Tests

open Bytes
open Lean (Json)
open Libp2p.Identity
open Multiformats (Multiaddr)

/-- The go-libp2p peer id of the EIP-778 key. -/
private def examplePeerId : String := "16Uiu2HAmSH2XVgZqYHWucap5kuPzLnt2TsNQkoppVxB5eJGvaXwm"

/-- The items of an encoded record. -/
private def itemsOf (wire : ByteArray) : List Rlp.Item :=
  match Rlp.decode? (toNatList wire) with
  | .ok (v, _) => v.item.list?.getD []
  | .error _ => []

/-- A record from its items. -/
private def wireOf (items : List Rlp.Item) : ByteArray := ofNatList (Rlp.encode (.list items))

private def str (s : String) : Rlp.Item := .bytes (toNatList (ofString s))

/-- True when the decode fails with `e`, so the caller reads no pair. -/
private def refuses (e : Enr.Error) (wire : ByteArray) : Bool :=
  failsWith e (Enr.decode? wire)

/-- A binary multiaddr from its bytes. -/
private def maddr (bytes : List Nat) : Option Multiaddr :=
  (Multiaddr.ofByteArray? (ofNatList bytes)).toOption

private def bytesOfAddrs (ms : List Multiaddr) : List (List Nat) :=
  ms.map fun m => toNatList (Multiaddr.toByteArray m)

def Enr.run (r : Runner) : IO Unit := do
  r.section "enr" "ethereum/EIPs EIPS/eip-778.md"

  -- The EIP-778 record: it verifies, and every field reads back.
  let file := "enr-eip778.json"
  let j ← loadJson file
  let some wire := ofHex? (← jStr file j "recordHex") | r.check s!"{file} hex" false; return
  let some sig := ofHex? (← jStr file j "signatureHex") | r.check s!"{file} hex" false; return
  let nodeIdHex ← jStr file j "nodeIdHex"
  let seq ← jNat file j "seq"
  let mut pairs : List Enr.Pair := []
  for p in ← jArr file j "pairs" do
    let some k := ofHex? (← jStr file p "keyHex") | r.check s!"{file} hex" false; return
    let some v := ofHex? (← jStr file p "valueHex") | r.check s!"{file} hex" false; return
    pairs := pairs ++ [⟨.ofName (toNatList k), .bytes (toNatList v)⟩]
  match Enr.decode? wire with
  | .error e => r.check s!"{file}: the record verifies ({repr e})" false
  | .ok rec =>
    r.check s!"{file}: the record verifies" true
    r.check s!"{file}: seq" (rec.seq == seq)
    r.check s!"{file}: the signature" (rec.signature == toNatList sig)
    r.check s!"{file}: the pairs, in order" (rec.pairs == pairs)
    r.check s!"{file}: the node id" (toHex rec.nodeId == nodeIdHex)
    r.check s!"{file}: the record re-encodes to its bytes" (rec.encode == wire)
    r.check s!"{file}: ip is 127.0.0.1" (succeedsWith (some [127, 0, 0, 1]) rec.ip?)
    r.check s!"{file}: udp is 30303" (succeedsWith (some 30303) (rec.port? .udp))
    r.check s!"{file}: no tcp" (succeedsWith none (rec.port? .tcp))
    r.check s!"{file}: no ip6" (succeedsWith none rec.ip6?)

    -- The signer: the private key re-signs the example to its bytes.
    -- The nonce is RFC 6979, as in the go-ethereum signer of the text.
    let text ← jStr file j "recordText"
    let some priv := (ofHex? (← jStr file j "privateKeyHex")).bind Crypto.Key32.ofByteArray?
      | r.check s!"{file}: the private key" false; return
    let others := rec.pairs.filter fun p => p.key != .id && p.key != .secp256k1
    match Enr.sign priv seq others with
    | .error e => r.check s!"{file}: the example re-signs ({repr e})" false
    | .ok signed =>
      r.check s!"{file}: the example re-signs to the record's bytes" (signed.encode == wire)
    r.check s!"{file}: the signer replaces a stale id and key"
      ((Enr.sign priv seq rec.pairs).toOption.map Enr.encode == some wire)
    r.check s!"{file}: the signer refuses a repeated key"
      (failsWith .keyOrder (Enr.sign priv seq (others ++ [⟨.udp, .bytes [0x76, 0x5f]⟩])))
    let some zero := Crypto.Key32.ofByteArray? (ofNatList (List.replicate 32 0))
      | r.check "a 32-byte zero key" false; return
    r.check "the signer refuses the zero scalar"
      (failsWith .privateKey (Enr.sign zero seq others))
    r.check "the signer refuses a seq past 64 bits"
      (failsWith .seq (Enr.sign priv (2 ^ 64) others))
    let big : Enr.Pair := ⟨.other (toNatList (ofString "z")), .bytes (List.replicate 250 0)⟩
    r.check "the signer refuses a record over 300 bytes"
      (failsWith .tooLarge (Enr.sign priv seq (others ++ [big])))

    -- The text form: the example prints to its text and reads back.
    r.check s!"{file}: the record prints to the example text" (rec.toText == text)
    r.check s!"{file}: the example text reads to the record"
      ((Enr.ofText? text).toOption.map Enr.encode == some wire)
    r.check s!"{file}: the text without the enr: prefix is refused"
      (failsWith .text (Enr.ofText? (text.drop Enr.textPrefix.length).toString))
    let tfile := "enr-text-sigp.json"
    let tj ← loadJson tfile
    for c in ← jArr tfile tj "cases" do
      let name ← jStr tfile c "name"
      r.check s!"{tfile}: {name} is refused" (failsWith .text (Enr.ofText? (← jStr tfile c "text")))

    -- The mapping: the peer id go-libp2p derives, one address, and back.
    r.check s!"{file}: the peer id is go-libp2p's"
      ((rec.peerId.toOption.map Mock.Keys.PeerId.toBase58) == some examplePeerId)
    match rec.multiaddrs with
    | .error e => r.check s!"{file}: the multiaddrs ({repr e})" false
    | .ok addrs =>
      r.check s!"{file}: one multiaddr, /ip4/127.0.0.1/udp/30303"
        (bytesOfAddrs addrs == [[0x04, 127, 0, 0, 1, 0x91, 0x02, 0x76, 0x5f]])
      r.check s!"{file}: the multiaddrs map back to the address pairs"
        (succeedsWith rec.addressPairs (Enr.pairsOfMultiaddrs addrs))

    -- The forward map of a dual-stack record: the IPv6 address takes
    -- `tcp6`, and `udp` where the record has no `udp6`.
    let v6 := List.replicate 15 0 ++ [1]
    let port (p : Nat) : List Nat := [p / 256, p % 256]
    let dual : List Enr.Pair := [⟨.ip, .bytes [1, 2, 3, 4]⟩, ⟨.ip6, .bytes v6⟩,
      ⟨.tcp, .bytes (Rlp.ofScalar 9000)⟩, ⟨.tcp6, .bytes (Rlp.ofScalar 9100)⟩,
      ⟨.udp, .bytes (Rlp.ofScalar 9001)⟩]
    match Enr.sign priv 1 dual with
    | .error e => r.check s!"the dual-stack record signs ({repr e})" false
    | .ok drec =>
      r.check "dual stack: four multiaddrs, the IPv6 ones over tcp6 and udp"
        (succeedsWith
          [[0x04, 1, 2, 3, 4, 0x06] ++ port 9000, [0x04, 1, 2, 3, 4, 0x91, 0x02] ++ port 9001,
            (0x29 :: v6) ++ [0x06] ++ port 9100, (0x29 :: v6) ++ [0x91, 0x02] ++ port 9001]
          (drec.multiaddrs.map bytesOfAddrs))
      r.check "dual stack: the multiaddrs map back to the address pairs"
        (succeedsWith drec.addressPairs (drec.multiaddrs >>= Enr.pairsOfMultiaddrs))

  -- One rejection per decode rule. Each mutation starts from the
  -- example's items: `[signature, seq, id, v4, ip, …, udp, 765f]`.
  let items := itemsOf wire
  let swapAt (i : Nat) (v : Rlp.Item) : List Rlp.Item := items.set i v
  r.check "a tampered udp value fails the signature, so no pair is read"
    (refuses .signature (wireOf (swapAt 9 (.bytes [0x76, 0x60]))))
  let s := Rlp.beNat ((toNatList sig).drop 32)
  let highS := (toNatList sig).take 32 ++ Rlp.beBytes (Ecdsa.secp256k1Order - s)
  r.check "the high-S twin of the signature fails"
    (refuses .signature (wireOf (swapAt 0 (.bytes highS))))
  r.check "a 63-byte signature fails"
    (refuses .signature (wireOf (swapAt 0 (.bytes ((toNatList sig).take 63)))))
  r.check "a record over 300 bytes is refused before the RLP decode"
    (refuses .tooLarge (ofNatList (List.replicate 301 0xc0)))
  r.check "a byte after the record is refused"
    (refuses .trailing (wire ++ ofNatList [0x80]))
  r.check "a string in place of the list is refused" (refuses .shape (ofNatList [0x80]))
  r.check "a seq with a leading zero is refused"
    (refuses .seq (wireOf (swapAt 1 (.bytes [0x00, 0x01]))))
  r.check "keys out of order are refused"
    (refuses .keyOrder (wireOf (swapAt 2 (str "ip") |>.set 4 (str "id"))))
  r.check "a repeated key is refused"
    (refuses .keyOrder (wireOf (swapAt 4 (str "id"))))
  r.check "an id other than v4 is refused" (refuses .scheme (wireOf (swapAt 3 (str "v5"))))
  r.check "a record without an id is refused"
    (refuses .scheme (wireOf ((items.take 2) ++ items.drop 4)))
  r.check "a 32-byte secp256k1 key is refused"
    (refuses .publicKey (wireOf (swapAt 7 (.bytes ((List.replicate 32 0x03))))))
  r.check "the RLP error reaches the caller"
    (refuses (.rlp .truncated) (ofNatList [0xc3, 0x80]))

  -- The reverse map of a dual-stack node. The IPv6 port that equals
  -- the IPv4 port stays general; a different one is `tcp6`.
  let ip4 := [0x04, 1, 2, 3, 4]
  let ip6 := 0x29 :: List.replicate 15 0 ++ [1]
  let tcp (p : Nat) := [0x06, p / 256, p % 256]
  let udp (p : Nat) := [0x91, 0x02, p / 256, p % 256]
  let pair (k : Enr.Key) (b : List Nat) : Enr.Pair := ⟨k, .bytes b⟩
  match [ip4 ++ tcp 9000, ip6 ++ tcp 9000, ip6 ++ udp 9001].mapM maddr with
  | none => r.check "the dual-stack multiaddrs build" false
  | some addrs =>
    r.check "dual stack: ip, ip6, a general tcp, and the IPv6 udp as general"
      (succeedsWith [pair .ip [1, 2, 3, 4], pair .ip6 (List.replicate 15 0 ++ [1]),
          pair .tcp (Rlp.ofScalar 9000), pair .udp (Rlp.ofScalar 9001)]
        (Enr.pairsOfMultiaddrs addrs))
  match [ip4 ++ tcp 9000, ip6 ++ tcp 9100].mapM maddr with
  | none => r.check "the tcp6 multiaddrs build" false
  | some addrs =>
    r.check "dual stack: a different IPv6 tcp port is tcp6"
      (succeedsWith [pair .ip [1, 2, 3, 4], pair .ip6 (List.replicate 15 0 ++ [1]),
          pair .tcp (Rlp.ofScalar 9000), pair .tcp6 (Rlp.ofScalar 9100)]
        (Enr.pairsOfMultiaddrs addrs))
  match [ip4 ++ tcp 9000, ip4 ++ tcp 9001].mapM maddr with
  | none => r.check "the conflicting multiaddrs build" false
  | some addrs =>
    r.check "two IPv4 tcp ports conflict"
      (failsWith (.value .tcp) (Enr.pairsOfMultiaddrs addrs))

end Tests
