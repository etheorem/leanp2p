import LeanP2P.Crypto.Multihash
import LeanP2P.Crypto.Multibase
import LeanP2P.Crypto.Base58
/-!
# CID

Content identifiers (multiformats/cid):

- v0 is a bare sha2-256 multihash (no version or codec prefix); its text
  form is base58btc (`Qm...`);
- v1 is `<0x01><varint codec><multihash>`; its canonical text form here is
  multibase base32 lower (`b...`), which is what the peer-ids spec uses for
  `libp2p-key` peer ids (`bafz...`).

Peer-id parsing in multiaddr accepts both: the multihash is what goes on
the wire (go-multiaddr stores `c.Hash()`), and the form flag decides how
the value is printed back (Go always prints base58; JS prints the CIDv1
form it parsed - we store the form so both suites round-trip).
-/

namespace LeanP2P.Cid

def codecLibp2pKey : Nat := 0x72
def codecDagPb : Nat := 0x70

inductive Cid where
  | v0 (mh : Multihash.Multihash)
  | v1 (codec : Nat) (mh : Multihash.Multihash)
deriving Repr, BEq

/-- Wire bytes. -/
def toBytes : Cid → List Nat
  | .v0 mh => Multihash.encode mh
  | .v1 codec mh => 0x01 :: Varint.encode codec ++ Multihash.encode mh

def mhOf : Cid → Multihash.Multihash
  | .v0 mh => mh
  | .v1 _ mh => mh

/-- Decode wire bytes. v0 is detected by the leading sha2-256 multihash
header `12 20` (there is no version byte). -/
def ofBytes? (bs : List Nat) : Option Cid := do
  if bs.take 2 = [Multihash.codeSha256, 32] then
    let mh ← Multihash.decode? bs
    some (.v0 mh)
  else do
    let 0x01 :: rest ← pure bs | none
    let (codec, rest) ← Varint.decode? rest
    let mh ← Multihash.decode? rest
    some (.v1 codec mh)

/-- Canonical text form: v0 → base58btc, v1 → multibase base32 lower. -/
def toString (c : Cid) : String :=
  match c with
  | .v0 mh => Base58.encode (Multihash.encode mh)
  | .v1 codec mh =>
      Multibase.encode .base32 (Bytes.ofNatList (toBytes (.v1 codec mh)))

/-- Parse a CID string: `Qm...` v0 form, anything else through multibase. -/
def ofString? (s : String) : Option Cid := do
  if s.startsWith "Qm" then
    let bs ← Base58.decode? s
    ofBytes? bs
  else do
    let (_, bytes) ← Multibase.decode? s
    ofBytes? (Bytes.toNatList bytes)

/-- The CIDv1 libp2p-key form of a peer multihash (`bafz...`). -/
def libp2pKeyV1 (mh : Multihash.Multihash) : Cid :=
  .v1 codecLibp2pKey mh

end LeanP2P.Cid
