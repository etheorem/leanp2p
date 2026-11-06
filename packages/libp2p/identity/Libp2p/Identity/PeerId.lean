import Libp2p.Identity.Keys

/-!
# Peer ids

A peer id is a multihash of the marshaled public key (the peer-ids spec,
"Peer Ids"). A marshaled key of at most `maxInlineKeyBytes` (42)
inlines as an identity multihash, so the id carries the key itself; a
longer key hashes with sha2-256. Every Ed25519 key marshals to 36
bytes, so every Ed25519 id inlines, and its base58btc text starts with
`12D3KooW`. An RSA key marshals to hundreds of bytes, so its id hashes,
and its text starts with `Qm`.

`PeerId` is a proof-carrying newtype (ARCHITECTURE §3.7): the multihash,
the fact that it has the peer id shape, and the text form the id was
parsed in. The shape rule has one home,
`Multiformats.Multiaddr.validPeerHash`, which the `p2p` component reads
too. Every constructor checks the shape once, where the bytes enter, and
no consumer checks it again (owned contract 4).

**The text forms.** The spec names two (peer-ids, "String
representation"): the legacy base58btc multihash (`Qm…`, `12D3KooW…`)
and a CIDv1 under the `libp2p-key` codec in multibase (`bafz…` in
base32). The multicodec table of `codec/multiformats` names that codec
`p2p-key`, code `0x72`. Parsing follows the decoding rule of the spec
(peer-ids, "Decoding"): a text that starts with `1` or `Qm` is a bare
base58btc multihash, and any other text is a multibase CID. go prints
the base58btc form, and js prints the CIDv1 form. The package stores
the parsed form and prints it back (owned contract 6, PRINCIPLES 2.1).
An id derived from a key or decoded from bytes records the base58btc
form, the go form. A form with no text for the multihash never enters
(`printable`), so `ToString` is total. Proquint is the one base with
such a gap: it writes only an even number of bytes.

**Comparing peer ids.** The spec defines the peer id as the multihash:
"extract the multihash from the CID. This is the peer ID" (peer-ids,
"Decoding"). Two values name the same peer when their multihashes are
equal, so code that asks "is this the same peer?" compares `a.hash ==
b.hash` (or `a.toBytes == b.toBytes`). The derived `==` also compares
the recorded form, so the `Qm…` and `bafz…` texts of one peer are
unequal under it.
-/

set_option autoImplicit false

namespace Libp2p.Identity

open Bytes Multiformats
open Multiformats.Multibase (Base)

/-- The text form of a peer id. -/
inductive PeerIdForm where
  /-- The legacy base58btc multihash. -/
  | base58
  /-- The CIDv1, in this multibase. -/
  | cid (base : Base)
  deriving DecidableEq, Repr, Hashable, Ord

/-- The CIDv1 of a multihash under the `libp2p-key` codec. -/
def keyCid (m : Multihash) : Cid := .v1 .«p2p-key» m

/-- The text of a multihash in a form; `none` when the form has no text
for it, which only the proquint base reaches. -/
def PeerIdForm.text? (m : Multihash) : PeerIdForm → Option String
  | .base58 => some (Base58.encode m.toByteArray)
  | .cid base => (Multibase.encode? base (keyCid m).toByteArray).toOption

/-- A validated peer id: a multihash of the peer id shape, and the text
form it prints in. Compare peer ids with `a.hash == b.hash` (the module
docstring, "Comparing peer ids"). -/
structure PeerId where
  /-- The multihash: identity over the marshaled key, or sha2-256 of it. -/
  hash : Multihash
  /-- The multihash has the peer id shape. -/
  shape : Multiaddr.validPeerHash hash = true
  /-- The text form the id was parsed in; base58btc for a derived id. -/
  form : PeerIdForm
  /-- The form has a text for the multihash, so `toString` is total. -/
  printable : (form.text? hash).isSome = true
  deriving DecidableEq, Repr, Hashable, Ord

namespace PeerId

/-! ## Construction -/

/-- The peer id of a multihash in a form, when the multihash has the
peer id shape and the form has a text for it (`PeerIdForm.text?`). A
form with no text is `badBaseValue`. -/
def ofMultihash? (m : Multihash) (form : PeerIdForm := .base58) : Except Error PeerId :=
  if h : Multiaddr.validPeerHash m then
    if hp : (form.text? m).isSome then .ok ⟨m, h, form, hp⟩
    else .error (.peerIdCodec .badBaseValue)
  else .error .notPeerShape

/-- The peer id of its binary form, the multihash bytes, as a `p2p`
multiaddr component or a Noise payload carries it. -/
def ofBytes? (b : ByteArray) : Except Error PeerId := do
  ofMultihash? (← (Multihash.ofByteArray? b).mapError .peerIdCodec)

/-- The binary form: the multihash bytes. -/
def toBytes (p : PeerId) : ByteArray := p.hash.toByteArray

/-- The inlined peer id of a marshaled key at most `maxInlineKeyBytes`
long: the identity multihash, whose digest is the key itself. The size
bound proves the digest within the cap, and the identity code proves
the shape. -/
def inline (b : ByteArray) (h : b.size ≤ maxInlineKeyBytes) : PeerId where
  hash := {
    code := .«identity»
    digest := toNatList b
    valid := fun _ hx => ltOfMemToNatList hx
    bounded := by
      rw [lengthToNatList]
      simp only [maxInlineKeyBytes] at h
      simp only [maxDigestBytes]
      omega }
  -- The first disjunct of `validPeerHash` compares the identity code
  -- with itself, so `simp` closes it without the hash table.
  shape := by simp [Multiaddr.validPeerHash]
  form := .base58
  printable := rfl

/-- The hashed peer id of a sha2-256 digest. `none` for a digest that is
not 32 bytes, which the facade's SHA-256 never returns. -/
def ofSha256? (d : ByteArray) : Option PeerId :=
  if h : d.size = 32 then
    some {
      hash := {
        code := .«sha2-256»
        digest := toNatList d
        valid := fun _ hx => ltOfMemToNatList hx
        bounded := by rw [lengthToNatList, h]; simp [maxDigestBytes] }
      shape := by simp [Multiaddr.validPeerHash, lengthToNatList, h]
      form := .base58
      printable := rfl }
  else none

/-- The peer id of a marshaled public key: inlined at the threshold and
below, hashed with sha2-256 above it (owned contract 3). -/
def ofMarshaled (b : ByteArray) : Except Error PeerId :=
  if h : b.size ≤ maxInlineKeyBytes then .ok (inline b h)
  else do
    let d ← (Crypto.sha256 b).mapError .crypto
    match ofSha256? d with
    | some p => return p
    | none => throw (.crypto .fault)

/-- A key at the threshold or below inlines. The hashed branch is the
facade's SHA-256, so the vectors pin that side (CLAUDE.md, "Proofs and
tests"). -/
theorem ofMarshaledInline {b : ByteArray} (h : b.size ≤ maxInlineKeyBytes) :
    ofMarshaled b = .ok (inline b h) := by
  simp [ofMarshaled, h]

/-- The peer id of a public key, over its deterministic marshaling. The
key passed the strict check when it was built, so a key with a bad
`Data` size never reaches this function (owned contract 2). -/
def ofPubKey (k : PubKey) : Except Error PeerId := ofMarshaled k.marshal

/-! ## Text -/

/-- The CIDv1 of the peer id, under the `libp2p-key` content codec. -/
def toCid (p : PeerId) : Cid := keyCid p.hash

/-- The text of the peer id in a form; `none` when the form has no text
for it (`PeerIdForm.text?`). -/
def toText? (p : PeerId) (form : PeerIdForm) : Option String := form.text? p.hash

/-- The text in the recorded form. Printing gives the canonical text of
that form, so a parsed text prints back to itself. The `printable`
field proves the text exists. -/
def toString (p : PeerId) : String := (p.form.text? p.hash).get p.printable

instance : ToString PeerId := ⟨PeerId.toString⟩

/-- The multihash of a peer id text, and the multibase of a CID text, by
the decoding rule of the spec (peer-ids, "Decoding"): a text that starts
with `1` or `Qm` is a bare base58btc multihash; any other text is a
multibase CIDv1, and its codec must be `libp2p-key`. -/
def textHash? (s : String) : Except Multiformats.Error (Option Base × Multihash) := do
  if s.startsWith "1" || s.startsWith "Qm" then
    return (none, ← Multihash.ofByteArray? (← Base58.decode? s))
  else
    let (base, bytes) ← Multibase.decode? s
    match ← Cid.ofByteArray? bytes with
    | .v1 .«p2p-key» m => return (some base, m)
    | _ => throw .badCid

/-- A peer id of either text form (`textHash?`), then the shape check.
The id records the form of the text. -/
def ofString? (s : String) : Except Error PeerId := do
  let (base?, m) ← (textHash? s).mapError .peerIdCodec
  ofMultihash? m (match base? with
    | none => .base58
    | some base => .cid base)

end PeerId

end Libp2p.Identity
