# leanp2p identity: architecture

`libp2p/identity` holds the four libp2p key types, their protobuf
marshalings, the strict unmarshal, and `PeerId` (ARCHITECTURE §4.9).
It also owns the key-marshal forms that the crypto backend leaves out
on purpose: the SEC1/SPKI/PKCS#1 choices and the key-type protobuf
(§4.6, §10 row 7; the backend pair records the split from its side).
The package sits at the bottom of the libp2p group. `libp2p/core`
imports it for `PeerId`, and nothing in it knows a connection (§2,
§4.9). W6.1 adds the ENR side (PLAN W6.1).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Identity.lean` | the root module; one import line per public submodule |
| `Libp2p/Identity/Constants.lean` | the 42-byte inlining threshold, the per-type `Data` lengths, and the DER minima; one home per fact (PRINCIPLES 1.5) |
| `Libp2p/Identity/KeyType.lean` | the closed set (§3.4): four constructors, `toCode`/`ofCode?`, and the `ofCode?_toCode` theorem |
| `Libp2p/Identity/Error.lean` | the package error type, preserving protobuf, crypto, and multiformats failures |
| `Libp2p/Identity/Marshal.lean` | writers for the per-type `Data` forms, the backend byte selection, and the Type/Data protobuf field table and encoding |
| `Libp2p/Identity/Keys.lean` | `PubKey` and `PrivKey`, their validity rules and checked constructors, the thin `ProtoMessage` instances and marshal/unmarshal entry points, and the sign/verify/derive dispatch |
| `Libp2p/Identity/Unmarshal.lean` | protobuf decoding and field extraction; calls the checked key constructor before returning a key |
| `Libp2p/Identity/PeerId.lean` | derivation over the marshaled key, identity inlining, and the text forms |
| `Libp2p/Identity/Rlp.lean` | the wrapper over the imported RLP library: the `Codec` instances, the error mapping, and the surface; the codec itself comes from the etheorem monorepo |
| `Libp2p/Identity/Enr.lean` | the ENR record, its typed pairs, and the signature check |
| `Libp2p/Identity/Enr/Mapping.lean` | the peer-id mapping and the multiaddr mapping |

All declarations live in the `Libp2p.Identity` namespace, and the root
module re-exports the public submodules. The spike reference for this
side is `Crypto/Keys.lean` and `Crypto/PeerId.lean` (§10 row 11);
`Crypto/OpenSsl.lean` carries the key forms on the backend side
(§10 row 7).

## Public surface

- `KeyType` is the closed set of §3.4: `rsa` (0), `ed25519` (1),
  `secp256k1` (2), `ecdsa` (3), with `toCode`, `ofCode?`, and the
  `ofCode?_toCode` theorem that `decide` closes. The standard classes
  derive (§3.2).
- `PubKey` and `PrivKey` carry a key type and `Data` bytes. The strict
  unmarshal builds them, so a constructed key already fits its type
  (§3.7); sign and derive re-check nothing. Each key also carries the
  protobuf payload bounds, so its `ProtoMessage` encoder is total.
  The validity rules live with the key definitions. `Unmarshal` receives
  their checked constructor as an argument; it does not repeat the rules.
- `PubKey.ofData?` and `PrivKey.ofData?` return `Except Error`.
  The package's `Error` distinguishes missing fields, unsupported key
  types, invalid Data, and inconsistent public halves. Dependency errors
  retain their original value under `protobuf`, `crypto`, or `encoding`.
  The generic `ProtoMessage` instances use the class's `Pb.Error`:
  wire errors remain exact, and identity validation maps to `badField`.
  The identity unmarshal functions preserve the precise package error.
- Sign, verify, and derive go through the `Crypto` facade (§3.6). The
  schemes are the peer-ids spec's: Ed25519 signs the raw message
  (RFC 8032), and the three DER schemes hash with SHA-256 first and
  sign over the digest: secp256k1 with BIP-62 low-S, ECDSA P-256, and
  RSA RSASSA-PKCS1-v1_5. Which schemes draw a random nonce is the
  backend's binding table (§3.6).
- `PrivKey.sign : PrivKey → ByteArray → ExceptT Error IO ByteArray`
  preserves signing errors and carries P-256's random nonce draw. The
  deterministic schemes lift their pure result into the same surface.
  `PubKey.verify : PubKey → ByteArray → ByteArray → Bool` stays pure
  and returns false for malformed inputs, signature mismatches, and
  backend faults. Both functions pass the original message to the
  facade, which owns each scheme's hashing.
- `derivePubKey : PrivKey → Except Error PubKey` selects
  `Crypto.ed25519PublicKey`, `Crypto.secp256k1PublicKey`,
  `Crypto.rsaPublicKey`, or `Crypto.p256PublicKey`. Ed25519 passes the
  seed and secp256k1 passes the scalar, each as `Key32` with a size
  proof from the private key. RSA and P-256 pass their stored DER.
  The returned bytes enter through `PubKey.ofData?`, which reports an
  unexpected public shape as `invalidKeyData`.
- The `Keys` protobuf message has the field table of the peer-ids
  spec: field 1 `Type`, a varint, and field 2 `Data`, bytes. The
  `ProtoMessage` instances live here, next to the message types
  (§3.2, §4.5; the `codec/proto` pair owns the wire codec and the
  class). The marshalings are deterministic, and the per-type `Data`
  forms are:

  | KeyType | public `Data` | private `Data` |
  |---|---|---|
  | Ed25519 | raw, 32 bytes | 64-byte seed‖public; 32-byte seed and the legacy 96-byte seed‖public‖public are accepted on unmarshal |
  | secp256k1 | SEC1 compressed point, 33 bytes | 32-byte scalar |
  | ECDSA P-256 | SPKI DER | SEC1 (RFC 5915); PKCS#8 is accepted on import |
  | RSA | SPKI DER | PKCS#1 DER |

  The Ed25519 private form is the seed‖public envelope the peer-ids
  spec vector itself carries.
  `Marshal` assembles Ed25519 seed/public bytes, compressed secp256k1
  points, RSA SPKI/PKCS#1 DER, and P-256 SPKI/SEC1 DER from supplied
  components. The writers do not generate or cryptographically validate
  keys. Ed25519 public bytes and secp256k1 private scalars need no
  additional encoding. Ed25519 imports normalize to 64-byte seed‖public
  envelopes. Construction derives the public half and checks any supplied
  copies against it. P-256 imports normalize to SEC1 through
  `Crypto.p256Sec1`; RSA requires PKCS#1 through `Crypto.rsaPkcs1`.
  This makes exported private keys readable by go-libp2p's loaders.
  `backendData` selects the Ed25519 seed and otherwise passes stored Data.
  The backend owns DER parsing and re-encoding through the facade.
- `PeerId` is a validated multihash (§3.7): the peer-ids shape over
  the marshaled public key. A marshaled key of at most 42 bytes
  inlines as an identity multihash, so every Ed25519 id is a
  `12D3KooW...` id; a larger key hashes with sha2-256. The text forms
  are the legacy base58btc multihash (`Qm...`) and the CIDv1
  `libp2p-key` multibase form (`bafz...`); parsing accepts both, and
  base36 is accepted beside base32. `BEq`, `Hashable`, and `Ord` use
  the multihash alone, so different text forms name the same runtime
  key (§3.2's exception for spec behavior). `DecidableEq` and `Repr`
  derive over the stored representation. `ToString` prints the
  recorded form (the decision below).
- The ENR surface (PLAN W6.1): `Rlp` encodes and decodes through the
  imported library, behind a `Codec` instance and its law. `Enr`
  holds the record as a sequence number and typed pairs; the known
  keys (`secp256k1`, `id`, `ip`, `tcp`, `udp`) are named constructors
  (PRINCIPLES 1.9). The pairs serialize in sorted key order, and the
  signature covers that content. EIP-778 fixes the record format and
  the `v4` identity scheme, and the discv5 specification's ENR
  section names the `ip6`, `tcp6`, and `udp6` keys the mapping may
  need. Under `v4`, the record signs the keccak-256 digest of the
  RLP content with secp256k1, and the signature carries a recovery
  byte. The digest routes to `LeanHazmatKeccak` through the `Crypto`
  facade (§3.6; root §4.6).
  `Enr` verifies the signature before a caller reads a pair (§5.2;
  PRINCIPLES 2.4). `Enr/Mapping` maps the `secp256k1` entry to the
  peer id and the address entries to a `Multiaddr` (§8, "ENR ↔
  multiaddr/peer-id mapping").

## Owned contracts and how the package keeps them

1. **Deterministic marshalings.** Same key, same bytes, every time.
   The `ProtoMessage` instances emit in the field table's fixed order
   with minimal varints, and `codec/proto` makes that deterministic
   by construction (`codec/proto` docs). The suite marshals one key
   of each type twice and asserts the bytes are equal.
   `Unmarshal.keyFieldsRoundTrip`, `PubKey.ofFieldsToFields`, and
   `PubKey.decodeEncode` prove field extraction and the public-key
   round trip over the protobuf byte model in the kernel.
2. **Strict unmarshal before derivation.** A `Data` length that does
   not fit the key type is a rejection, before any id derives from
   the key (§4.9, §5.2; PRINCIPLES 2.4). The spike records the
   reason: a truncated key would still derive a well-formed but bogus
   peer id. The public table demands 32 bytes for Ed25519 and 33 for
   secp256k1, with SEC1 prefix `0x02` or `0x03`. A 31-byte Ed25519 key
   cannot derive an id. The
   private table demands 32, 64, or 96 bytes for Ed25519 and 32 for
   secp256k1. The two public-key copies of a legacy 96-byte Ed25519
   private key must agree before construction, per the peer-ids spec.
   Every supplied Ed25519 public half must also match the seed's
   derived public key. Public DER passes a shell check: at least
   8 bytes and a leading `0x30`. Private DER crosses the backend's
   loader at construction, before the normalized export is stored.
   The backend retains the RSA 2048 to 8192 bit rule. Verifiers own
   signature checks, including secp256k1 low-S (§4.6).
3. **Identity inlining follows the spec threshold.** The 42-byte
   threshold sits in `Constants.lean` as the one home of the number.
   A key at the threshold inlines; a key one byte over hashes (§4.9).
4. **`PeerId` carries its proof.** It is a proof-carrying newtype
   over a validated multihash (§3.7), so a `PeerId` value in the
   stack has already passed the peer-multihash check. No consumer
   re-checks it.
5. **The ENR signature gates the pairs.** The signature verifies
   through the facade before the pairs are readable (§5.2;
   PRINCIPLES 2.4), and a record that fails the check yields no
   pairs. The scheme's specification is silent on low-S, so a `v4`
   signature makes no low-S promise, and it carries a recovery byte,
   as the Ethereum signing convention does. The secp256k1 verifier
   behind the facade rejects high-S signatures (§4.6), so the ENR
   module verifies
   through the recovery path or normalizes S locally, behind its own
   function. This is the one documented exception to the low-S rule:
   the discv5 specification fixes the scheme, and weakening the
   shared verifier would touch every caller.
6. **The print form is the recorded decision.** Go prints the legacy
   base58btc form and js prints the CIDv1 form. The package stores
   the parsed form and prints it back (PRINCIPLES 2.1), so parsing a
   string twice round-trips to the same string. A derived `PeerId`
   records the base58btc form, the go form, so `ToString` is total.
   Runtime equality, hashing, and ordering ignore that presentation
   metadata, so a peerstore lookup succeeds across text forms.
   Propositional equality still includes the stored representation;
   the type therefore makes no `LawfulBEq` claim.
   `codec/multiformats` fixes the same rule for its `p2p` component
   and hands the peer-id side to this package.

## Decisions

- **The marshalings live here.** The key forms are libp2p facts: the
  peer-ids spec fixes the protobuf and the per-type choices. The
  backend takes key bytes in and gives key bytes out, and its EVP
  surface keeps no opinion about the forms (§4.6, §10 row 7). The
  backend pair records the same split from its side.
- **The four-type surface includes RSA and ECDSA P-256.** Consensus
  defers both host keys, and go-libp2p interop needs them, so they
  stay in the surface that W5.1 closes (§8).
- **The ENR side lives here.** Root PLAN W6.1 assigns it to
  `libp2p/identity`, next to the keys it signs with and the peer id
  it maps to. discv5 itself stays out of scope (§8). EIP-778 and the
  discv5 specification's ENR section govern the surface, and the
  spike branch vendors neither text under `vendor/specs`. Landing
  unit 2 starts by vendoring both texts and committing the record
  fixture with recorded provenance, the way the backend plan handles
  its generated certificates. The keccak-256 digest routes to
  `LeanHazmatKeccak` (the etheorem package), per the root §4.6 origin
  split, and the route is one facade line (§3.6).
- **RLP is imported from etheorem.** Root PLAN W6.1 takes the RLP
  codec from the etheorem monorepo (`etheorem/etheorem`), the Lean 4
  consensus implementation this stack targets. The owner picked it
  over writing a fourth codec. Its facts, recorded: the RLP package
  is upstream work and not yet on its `main` (the monorepo says
  per-package publication repos will exist later); the license is
  LGPL-3.0 with a contributor agreement; the monorepo pins Lean
  v4.34.1 against this repo's v4.34.0. Unit 2 tracks the package,
  checks the toolchain skew, and wraps it behind the `Codec` surface
  and the package's own error mapping, with no second RLP. The
  recorded fallback, should the upstream not land in time or the
  skew not close, is the package's own small RLP.
- **DER parsing stays behind the facade.** Public keys pass a shell
  check before peer-id derivation. Private keys use the backend loader
  to validate and export the required form at construction. Identity
  carries no second DER parser (§4.6).

## What the package must not depend on

- Nothing inside libp2p. The package is the bottom of the group;
  `libp2p/core` imports it, and the reverse import is a lint failure
  (§2). No seam type, no `ProtocolId`, no connection.
- From crypto, the `Crypto` facade only (§3.6). No `crypto/backend`
  and no `crypto/pure` import, ever.
- From codec, `codec/proto` (the `Keys` field table and the class)
  and `codec/multiformats` (multihash, multibase, base58, CID, and
  multiaddr for the ENR mapping). The multiformats pair fixes the
  multihash this package validates over. `codec/varint` arrives
  through `codec/proto`.
- From base, `base/bytes` for the byte model. P-256 signing uses IO
  for its nonce. The package spawns no task and has no use for `base/conc`.
- One external Lean dependency, the etheorem monorepo's RLP package
  (`etheorem/etheorem`, LGPL-3.0), for the RLP wrapper, and no other.
  CLAUDE.md's dependency rule records it: the require block,
  `lake update`, the pinned git rev, and `lake-manifest.json`
  committed. Unit 2's first step is tracking the upstream package,
  which is not yet on the monorepo's `main`, and the v4.34
  toolchain-compat check of the pin (the monorepo pins v4.34.1). The
  recorded fallback is the package's own small RLP if the upstream
  does not land or the skew does not close.
