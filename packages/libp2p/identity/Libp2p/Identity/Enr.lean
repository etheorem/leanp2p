import Bytes
import Crypto
import Libp2p.Identity.Constants
import Libp2p.Identity.Rlp
import Libp2p.Identity.Rlp.Bytes
import Multiformats

/-!
# Ethereum Node Records

EIP-778 (`vendor/eips/EIPS/eip-778.md`). A node record is the RLP list
`[signature, seq, k, v, ...]`:

* `signature` covers the content `[seq, k, v, ...]` under the identity
  scheme the `id` pair names. EIP-778 defines one scheme, `v4`.
* `seq` is a 64-bit unsigned integer, a canonical RLP scalar.
* The pairs follow, sorted by key and unique. A key is a byte string;
  a value is any RLP item.

The encoded record holds at most 300 bytes, and the decoder checks that
cap before the RLP decode (PRINCIPLES 2.3).

## The `v4` scheme

The signer hashes the RLP content with keccak-256 and signs the hash
with secp256k1. The signature is `r ‖ s`, 64 bytes; EIP-778 omits the
recovery id `v`. The record carries the signer's compressed public key
in its `secp256k1` pair. Every primitive comes through the `Crypto`
facade: `keccak256` (`LeanHazmatKeccak`), `secp256k1SignDigest` (the
backend's RFC 6979 signer), and `secp256k1Recover`
(`LeanHazmatSecp256k1`).

The verifier recovers the public key from the hash and `(r, s)` for
each recovery id, compresses the result, and compares it with the
record's key. The recovery path works on the compressed key the record
holds, with no point decompression on this side. A high S is refused
before the recovery: go-ethereum (`crypto.VerifySignature`) and sigp/enr
(through libsecp256k1 and through k256) refuse it, and the low-S rule
of root ARCHITECTURE §4.6 agrees.

The signer nonce is RFC 6979, as in go-ethereum (libsecp256k1), so one
key and one content give one signature. The EIP-778 example re-signs
to its own bytes.

## Verify before read

`Enr` has a private constructor. `decode?` is the only function that
builds one, and it builds one only after the signature verifies.
`sign` returns the decode of the record it encodes, so a signed record
passes the same check. A caller that holds an `Enr` reads pairs that
the key in the record signed (package ARCHITECTURE, contract 5;
PRINCIPLES 2.4).

## The text form

`enr:`, then the base64url body of the encoded record, with no padding
(EIP-778, "RLP Encoding"; RFC 4648 §5). The body runs through the
`Multibase` codec of `codec/multiformats` under `base64url`, whose
decoder is canonical. The reader refuses a missing prefix, as
go-ethereum does. It refuses an `=` and non-zero trailing bits, as
sigp/enr does (package ARCHITECTURE, contract 7).
-/

set_option autoImplicit false

namespace Libp2p.Identity

open Bytes Rlp

/-! ## Keys -/

/-- An ENR key. The keys EIP-778 names are constructors; any other key
is `other`, with its bytes (PRINCIPLES 1.9). Build a key with
`Key.ofName`, which never wraps a known name in `other`. -/
inductive Enr.Key where
  | id
  | secp256k1
  | ip
  | tcp
  | udp
  | ip6
  | tcp6
  | udp6
  | other (name : List Nat)
  deriving DecidableEq, Repr

namespace Enr

/-- The bytes of a key. -/
def Key.name : Key → List Nat
  | .id => nameId
  | .secp256k1 => nameSecp256k1
  | .ip => nameIp
  | .tcp => nameTcp
  | .udp => nameUdp
  | .ip6 => nameIp6
  | .tcp6 => nameTcp6
  | .udp6 => nameUdp6
  | .other n => n

/-- The key of a name. -/
def Key.ofName (n : List Nat) : Key :=
  if n = nameId then .id
  else if n = nameSecp256k1 then .secp256k1
  else if n = nameIp then .ip
  else if n = nameTcp then .tcp
  else if n = nameUdp then .udp
  else if n = nameIp6 then .ip6
  else if n = nameTcp6 then .tcp6
  else if n = nameUdp6 then .udp6
  else .other n

/-- The conformance of the name table: every named key reads back from
its name, and `decide` closes each case. -/
theorem Key.ofNameName : ∀ (k : Key), (∀ n, k ≠ .other n) → Key.ofName k.name = k
  | .id, _ | .secp256k1, _ | .ip, _ | .tcp, _ | .udp, _ | .ip6, _ | .tcp6, _ | .udp6, _ => by
    decide
  | .other n, h => absurd rfl (h n)

/-- A key and its value. -/
structure Pair where
  key : Key
  value : Item
  deriving DecidableEq

/-- Why a record was refused. -/
inductive Error where
  /-- The encoding holds more than `maxRecordSize` bytes. -/
  | tooLarge
  /-- The RLP decode failed. -/
  | rlp (e : DecodeError)
  /-- Bytes follow the record. -/
  | trailing
  /-- The record is not a list of a signature, a `seq`, and pairs. -/
  | shape
  /-- `seq` is not a canonical 64-bit scalar. -/
  | seq
  /-- The keys are not sorted, or a key repeats. -/
  | keyOrder
  /-- The `id` pair is missing, or it names a scheme other than `v4`. -/
  | scheme
  /-- The `secp256k1` pair is missing, or it is not 33 bytes. -/
  | publicKey
  /-- The signature does not verify. -/
  | signature
  /-- A pair's value does not have the form its key requires. -/
  | value (k : Key)
  /-- The signer's private key is not a secp256k1 scalar in `[1, n - 1]`. -/
  | privateKey
  /-- The text lacks the `enr:` prefix, or its body is not canonical
  base64url. -/
  | text
  /-- A multiaddr is not an `ip4` or `ip6` address, then a `tcp` or `udp`
  port, the one shape a record holds. -/
  | multiaddr
  deriving DecidableEq, Repr

end Enr

/-- A node record whose `v4` signature verified. Only `Enr.decode?`
builds one; `Enr.sign` returns a decode. -/
structure Enr where
  private mk ::
  /-- The sequence number. -/
  seq : Nat
  /-- The pairs, sorted by key name. -/
  pairs : List Enr.Pair
  /-- The signature, `r ‖ s`. -/
  signature : List Nat
  /-- The `secp256k1` value: the compressed key that signed. -/
  publicKey : List Nat
  /-- The same key, uncompressed, `x ‖ y`. -/
  publicKeyXY : ByteArray

namespace Enr

/-! ## The `v4` scheme -/

/-- The compressed form of an uncompressed key `x ‖ y`: `0x02` for an
even `y`, `0x03` for an odd one, then `x`. The input is the 64-byte
point the recovery returns; `get! 63` reads the last byte of `y`. -/
def compress (xy : ByteArray) : List Nat :=
  (if (xy.get! 63).toNat % 2 = 0 then 0x02 else 0x03) :: toNatList (xy.extract 0 32)

/-- The uncompressed key that made `sig` over `content`, when it is
`publicKey`. `none` for a high S or a signature by another key. -/
def verifyV4 (content sig publicKey : List Nat) : Option ByteArray :=
  let hash := Crypto.keccak256 (ofNatList content)
  let r := ofNatList (sig.take 32)
  let s := sig.drop 32
  if halfOrder < beNat s then none
  else
    -- libsecp256k1 takes the recovery ids 0 to 3. Ids 2 and 3 cover
    -- an `R` whose x-coordinate is `r + n`, a case of probability
    -- about 2⁻¹²⁸. The search tries all four, so it accepts exactly
    -- the signatures a direct verify accepts.
    let candidates := [0, 1, 2, 3].map fun (recId : UInt32) =>
      Crypto.secp256k1Recover hash r (ofNatList s) recId
    candidates.find? fun xy => xy.size = 64 && compress xy == publicKey

/-! ## Decoding -/

/-- The pairs of a record, in order: a key string, then a value. Each
key sorts strictly after the one before it, so the keys are unique. -/
def pairsOf : List Item → Option (List Nat) → Except Error (List Pair)
  | [], _ => .ok []
  | [_], _ => .error .shape
  | k :: v :: rest, prev => do
    let some name := k.bytes? | .error .shape
    if let some p := prev then
      if !decide (p < name) then .error .keyOrder
    let tail ← pairsOf rest (some name)
    .ok (⟨Key.ofName name, v⟩ :: tail)

/-- The value of a key, if the record holds it. -/
def lookup (pairs : List Pair) (k : Key) : Option Item :=
  (pairs.find? (·.key == k)).map (·.value)

/-- Decode a record and verify its signature. -/
def decode? (b : ByteArray) : Except Error Enr := do
  if maxRecordSize < b.size then throw .tooLarge
  let (v, used) ← (decodeB? b).mapError .rlp
  if used != b.size then throw .trailing
  let some items := v.item.list? | throw .shape
  let sigItem :: contentItems@(seqItem :: kvs) := items | throw .shape
  let some sig := sigItem.bytes? | throw .shape
  let some seqBytes' := seqItem.bytes? | throw .shape
  let some seq := scalar? seqBytes seqBytes' | throw .seq
  let pairs ← pairsOf kvs none
  if lookup pairs .id != some (.bytes schemeV4) then throw .scheme
  let some (.bytes pub) := lookup pairs .secp256k1 | throw .publicKey
  if pub.length != publicKeySize then throw .publicKey
  if sig.length != signatureSize then throw .signature
  -- The content re-encodes to the bytes the signer hashed: the RLP
  -- decoder accepts canonical forms only (`Rlp.encodeDecodeAux`).
  let some xy := verifyV4 (encode (.list contentItems)) sig pub | throw .signature
  return ⟨seq, pairs, sig, pub, xy⟩

/-! ## Reading a verified record -/

/-- The value of a key in the record. -/
def get? (r : Enr) (k : Key) : Option Item := lookup r.pairs k

/-- The string value of `k` when it holds exactly `size` bytes. -/
def fixed? (r : Enr) (k : Key) (size : Nat) : Except Error (Option (List Nat)) :=
  match r.get? k with
  | none => .ok none
  | some (.bytes b) => if b.length = size then .ok (some b) else .error (.value k)
  | some (.list _) => .error (.value k)

/-- The IPv4 address, 4 bytes. -/
def ip? (r : Enr) : Except Error (Option (List Nat)) := r.fixed? .ip ip4Size

/-- The IPv6 address, 16 bytes. -/
def ip6? (r : Enr) : Except Error (Option (List Nat)) := r.fixed? .ip6 ip6Size

/-- A port: a canonical scalar of at most 2 bytes. -/
def port? (r : Enr) (k : Key) : Except Error (Option Nat) :=
  match r.get? k with
  | none => .ok none
  | some (.bytes b) =>
    match scalar? portBytes b with
    | some n => .ok (some n)
    | none => .error (.value k)
  | some (.list _) => .error (.value k)

/-- The node id of the `v4` scheme: keccak-256 of the uncompressed
public key `x ‖ y`. -/
def nodeId (r : Enr) : ByteArray := Crypto.keccak256 r.publicKeyXY

/-- The content `[seq, k, v, ...]` that the signature covers. -/
def contentItems (r : Enr) : List Item :=
  .bytes (ofScalar r.seq) :: r.pairs.flatMap fun p => [.bytes p.key.name, p.value]

/-- The encoded record. -/
def encode (r : Enr) : ByteArray :=
  ofNatList (Rlp.encode (.list (.bytes r.signature :: r.contentItems)))

/-! ## Signing -/

/-- Sign a record under the `v4` scheme with a raw secp256k1 scalar.

The signer sets `id` to `v4` and `secp256k1` to the compressed public
key of `scalar`, in place of any pair with those keys, as go-ethereum's
`SignV4` does (`vendor/go-ethereum/p2p/enode/idscheme.go`). It sorts the
pairs by key name, signs keccak-256 of the RLP content, and returns the
decode of the record. So the decoder's rules hold for the result: a
repeated key, a `seq` past 64 bits, and a record over 300 bytes are
refused. -/
def sign (scalar : Crypto.Key32) (seq : Nat) (pairs : List Pair) : Except Error Enr := do
  let pub ← (Crypto.secp256k1PublicKey scalar).mapError fun _ => .privateKey
  let own : List Pair := [⟨.id, .bytes schemeV4⟩, ⟨.secp256k1, .bytes (toNatList pub)⟩]
  let rest := pairs.filter fun p => p.key != .id && p.key != .secp256k1
  -- `mergeSort` keeps equal keys in order, so a repeated key reaches
  -- the decoder, which refuses it.
  let sorted := (own ++ rest).mergeSort fun a b => !decide (b.key.name < a.key.name)
  let content : List Item :=
    .bytes (ofScalar seq) :: sorted.flatMap fun p => [.bytes p.key.name, p.value]
  -- keccak-256 always gives 32 bytes, so the `none` arm is unreachable.
  let some digest := Crypto.Digest32.ofByteArray? (Crypto.keccak256 (ofNatList (Rlp.encode (.list content))))
    | throw .signature
  let sig ← (Crypto.secp256k1SignDigest scalar digest).mapError fun _ => .privateKey
  decode? (ofNatList (Rlp.encode (.list (.bytes (toNatList sig) :: content))))

/-! ## The text form -/

open Multiformats in
/-- The multibase text of the bytes under `base64url`. `Multibase.encode`
answers an `Except`, because Proquint refuses an odd byte count; the
`base64url` arm always answers `.ok`, so `simp` closes the other arm,
as `Multibase.encodeBase32` does for its base. -/
private def base64urlText (b : ByteArray) : String :=
  match h : Multibase.encode .base64url b with
  | .ok text => text
  | .error _ => by simp [Multibase.encode, Multibase.encode?, Bind.bind, Except.bind] at h

/-- The multibase prefix of `base64url`. The encoding of no bytes is
the prefix alone, so the prefix character is never written twice. -/
private def base64urlPrefix : String := base64urlText .empty

/-- The text form: `enr:`, then the base64url body of the encoding. -/
def toText (r : Enr) : String :=
  -- `String.drop` gives a `String.Slice`; `toString` copies it out.
  textPrefix ++ ((base64urlText r.encode).drop base64urlPrefix.length).toString

open Multiformats in
/-- Read a record from its text form, then decode and verify it. The
reader puts the `base64url` prefix in front of the body, so a decode
under any other base cannot occur; the arm refuses it all the same. -/
def ofText? (s : String) : Except Error Enr := do
  unless s.startsWith textPrefix do throw .text
  let body := (s.drop textPrefix.length).toString
  match Multibase.decode? (base64urlPrefix ++ body) with
  | .ok (.base64url, b) => decode? b
  | .ok _ => throw .text
  | .error _ => throw .text

end Enr

end Libp2p.Identity
