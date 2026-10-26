# leanp2p multiformats: architecture

`codec/multiformats` implements the multiformats family the stack
frames with: multihash, multibase, base58btc, CID v0 and v1, and
multiaddr (ARCHITECTURE §4.4). Peer ids go through multihash and CID.
Consensus dialing and the ENR mapping go through multiaddr. The
package carries its own conformance suites, so a project that uses it
without libp2p still runs them (§4.4).

## Modules

| Module | Holds, and why |
|---|---|
| `Multiformats.lean` | the root module; one import line per public submodule |
| `Multiformats/Constants.lean` | the decode caps: the largest digest, component value, and address length the decoders accept; one home per fact (PRINCIPLES 1.5) |
| `Multiformats/Tables.lean` | generated, committed source (§3.8): the multiaddr protocol table, the multibase registry table, and the multicodec slice this package consumes, each a closed inductive with `toCode`/`ofCode?` and the `ofCode?_toCode` theorem (§3.4) |
| `Multiformats/Base58.lean` | base58btc and base58flickr; each leading zero byte of the payload becomes one `1` character, per the spec |
| `Multiformats/Multibase.lean` | the full registry: one closed inductive `Base` over the multibase table, a prefix character per base, `encode` / `decode?` |
| `Multiformats/Multihash.lean` | the function table as a closed inductive, the proof-carrying `Multihash` type, the strict decode, the `Codec` instances |
| `Multiformats/Cid.lean` | CID v0 and v1, the text forms through multibase, the `Codec` instances |
| `Multiformats/Multiaddr.lean` | the component inductive over the protocol table and the validated `Multiaddr` type |
| `Multiformats/Multiaddr/Text.lean` | `parse?` and `toString`, with the percent codecs beside them |
| `Multiformats/Multiaddr/Binary.lean` | `toByteArray` and `ofByteArray?`, plus `Codec Multiaddr` |
| `Multiformats/Multiaddr/Ops.lean` | the operations API |

All declarations live in the `Multiformats` namespace. The root module
re-exports the public submodules.

The table generator is a Lean script, `scripts/gen-multiformats.lean`,
run with `lake env lean --run` (§3.8). It reads the vendored CSVs
(`protocols.csv`, `multibase.csv`, and the multicodec CSV) and writes
`Multiformats/Tables.lean`. The repository commits that file, and a
test re-derives it from the CSV and asserts the match.

`Base58` sits in its own module beside `Multibase`: base58 is a plain
integer-base transcoder with no prefix scheme, and the peer-id text
form and `Cid` use it without the other bases. The spike's
`Crypto/Base58.lean` carries base58btc only, and the flickr alphabet
sits in the spike's `Crypto/Multibase.lean`. Its modules
`Crypto/{Multihash,Multibase,Base58,Cid}.lean` and
`Net/Multiaddr.lean` are the reference for the whole package (§10,
row 4), and the strictness rules of §4.4 carry over.

## Public surface

The names are the root names (§7, row 5), shaped by the mechanisms of
§3:

- `Multihash` is a proof-carrying structure (§3.7): the function code,
  the digest, and a proof field that ties the digest length to the
  declared length. `Multihash.ofByteArray?` and `Codec Multihash`
  decode strictly, and `LawfulCodec Multihash` states the law.
- `Multibase` exposes `Base` (the closed registry), `encode : Base →
  ByteArray → String`, and `decode? : String → Except
  Multiformats.Error (Base × ByteArray)`. base58btc and base58flickr
  dispatch into `Base58`, whose `encode` and `decode?` over
  `ByteArray` turn each leading zero byte of the payload into one `1`
  character.
- `Cid` covers both versions: v0 is a bare sha2-256 multihash, and v1
  is `0x01`, a content codec, and a multihash. `Codec Cid` and
  `LawfulCodec Cid` exist, and the text forms run through `Multibase`.
- `Multiaddr` is a validated component list (§3.7), with `parse?`,
  `toString`, `toByteArray`, and `ofByteArray?` as the boundary
  functions (§7, row 5). The operations API takes the spike's shape,
  which the go and js operation vectors pin: `encapsulate`,
  `decapsulate`, `decapsulateCode`, `split`/`join`, `components`,
  `protocols`, `valueForProtocol`, `contains`, `unique`, and `filter`.
- The standard classes sit on `Multiaddr` (§3.2). `ToString` prints
  the text form of the spec, the case §3.2 allows hand-written.
- `Codec` instances exist for `Multiaddr`, `Multihash`, and `Cid`
  (§3.2). Each proves its `LawfulCodec` law, and the generic harness
  of `base/bytes` pins the `ByteArray` path once per instance.

## The proof-carrying boundaries

§3.7 lists `Multiaddr` among the proof-carrying types, and `Cid` and
`Multihash` validate at the boundary the same way. The decoder checks
the shape once and constructs the type. No core re-checks it. Each
boundary rejects:

- `Multihash`: an unknown function code, a digest cut below its
  declared length, trailing bytes past the declared digest, and a
  digest over the cap. A digest cut below its declared length routes
  through `framing`, so the reader sees `truncated` and keeps waiting.
  Trailing bytes past the declared digest are a spec violation and map
  to `malformed`, as does a digest over the cap. The length varint
  goes through the `codec/varint` boundary, so a non-minimal or
  over-long length is `malformed` before the digest check runs
  (`codec/varint` docs).
- `Cid`: a v0 prefix that is anything other than the sha2-256 shape, a
  v1 version byte other than `0x01`, a content codec outside the
  multicodec table, and an inner multihash that fails its own check.
- `Multiaddr`, text side: a missing leading `/`, an empty segment, a
  `_` digit separator, a leading-zero IPv4 octet, an unknown protocol
  name, and a value that fails its per-protocol check.
- `Multiaddr`, binary side: an unknown protocol code, a value length
  the input cannot yet satisfy, a value length the cap rejects, and a
  value that fails its per-protocol check. A value length the input
  cannot yet satisfy reports `truncated` through `framing`. A value
  that fails its per-protocol check or the cap reports `malformed`.
  `unix` is terminal: no component follows a path protocol.

## Owned contracts

1. **Strict text parsing.** The parser demands a leading `/`, rejects
   empty segments, `_` digit separators, and leading-zero IPv4 octets
   (§4.4). The reason: a lax parser accepts addresses the peer did not
   mean. The address feeds dialing and identity checks. The spike
   validated the rule against the go and js suites.
2. **Percent codecs over UTF-8 bytes.** A `%XX` escape carries a byte,
   and the decoder validates the result as UTF-8 (§4.4). An escape
   that encodes a code point emits wrong wire bytes for any non-ASCII
   path.
3. **The tables are generated, committed source.** The generator and
   the match test sit under "Modules" (§3.8), and the CSV is the one
   home of the table data.
4. **Bounded binary decode.** Every value length is checked against a
   cap from `Multiformats/Constants.lean` before allocation (§5.1;
   PRINCIPLES 2.3). A length the cap rejects is a protocol error, and
   the decoder never allocates for it.
5. **Round-trip and order.** The binary codecs prove round-trip over
   the model, as the `LawfulCodec` instances (§6; PRINCIPLES 5.1). The
   multiaddr binary form carries ordered components, so the decoder
   returns them in wire order and a decode-encode cycle is
   byte-exact. The doctrine is the amended §4.5 order rule, applied
   where the wire form is a sequence. The `ByteArray` paths are pinned
   to the model through the generic harness of `base/bytes`
   (`base/bytes` docs, owned contracts 1 and 2).

## The error boundary

`Multiformats.Error` is the one package-owned inductive (§3.5). One
type serves the whole package, because the decoders nest: a CID wraps
a multihash, a `p2p` component carries a multihash, and every length
goes through varint. It has a `framing` arm that carries `DecodeError`
verbatim, and one arm per boundary family: an unknown multihash
function code, a digest length mismatch, an unknown multibase prefix,
a payload that fails its base's alphabet, a CID version or content
codec outside the tables, and a failing multiaddr component. The
`Codec` instances map into `DecodeError`, the shared vocabulary of
every codec (§3.2; `base/bytes` docs). `framing e` maps to `e`. A
short input reaches `.malformed` only when it is a spec violation, and
a value the input can still complete reports `truncated` through
`framing`. Every other arm maps to `.malformed`, because a
strict-decode rejection is a spec violation and the reader stops
waiting (§5.2).

## Decisions

- **The `p2p` component prints the parsed form.** Go prints base58btc
  for every `p2p` value (its bytes-to-string transcoder is base58). Js
  prints base58btc from bytes and keeps a CIDv1 form it parsed. The
  wire value is the bare multihash. The parse stores which text form
  it came from, and printing returns that form. A binary decode prints
  base58btc, the go form. Both upstream suites round-trip under the
  rule. The peer-id print form itself belongs to `libp2p/identity`
  (PRINCIPLES 2.1); this document fixes only the multiaddr component.
- **`unix` and `http-path` differ.** `unix` stores its path verbatim,
  with no percent decoding. `http-path` stores the percent-decoded
  path and re-encodes it on print. Both follow go. The components view
  reports both decoded, as js does.
- **`memory` is a big-endian u64.** The vendored go-multiaddr parses
  `memory` as a u64 (`Size: 64` in its protocol table), and the `V`
  size in `protocols.csv` is stale. The spike's comment records that
  rust carries the same wire form. The discrepancy is recorded here
  rather than patched silently (PRINCIPLES 2.1). The two js vectors
  that carry a string value for `memory` are skipped in the suite as
  documented divergences.
- **Print-form details.** `parse? ""` fails, as go rejects it, and
  `toString` of the empty address is `/`, as js prints it.
  `::ffff:1.2.3.4` prints dotted, and every other IPv6 address prints
  RFC 5952 compressed.
- **Why the tables are committed.** §3.8: reviewers can read and grep
  a committed file. They cannot grep a macro expansion, and the tables
  follow upstream CSVs, so the diff of a table change must be visible.
- **Why the suites live in the library.** §4.4: a project that uses
  the package without libp2p still runs them. The vectors land through
  root W0.3, and the suite modules sit next to the code they pin.

## What the package must not depend on

- No import from a group above `codec`: no crypto, no net, no libp2p
  (ARCHITECTURE §2).
- Within the codec group, `codec/varint` only (§2, downward only). No
  `codec/proto`. The two packages are siblings in the graph.
- From `base`, `base/bytes` only: the `Codec` classes, `DecodeError`,
  and the harness. The package is pure; it spawns no task and holds no
  channel, so it has no use for `base/conc`.
- No libp2p knowledge: no peer id type, no protocol id, no key type
  (§4.4). The peer id is a validated multihash above this package
  (§3.7).
- No crypto. A multihash carries bytes a caller already digested; the
  digest functions live in the crypto group behind the `Crypto`
  facade (§3.6). The package owns the framing of a digest and nothing
  about computing one.
- No framing cap beyond its own decode caps. §5.1 puts the transport
  caps at the framing layers, and this package bounds its own reads
  through `Multiformats/Constants.lean`.
