# leanp2p multiformats: plan

This plan refines the root `docs/PLAN.md` for `codec/multiformats`.
The root plan owns the order across packages (PLAN.md, "How to read
this plan"). Unit 1 below is the root unit W2.3, and it depends on
W1.2 and W2.1. Its done-when is the root row plus the root definition
of done: the surface follows ARCHITECTURE §4.4, shaped by §3, the
owned contracts hold, the carried vector and property tests pass, the
suite passes under `+RTS -N1`, and the import lint is green.

## Units

Unit 1 splits into three sub-units. Each subcodec closes against its
own vector family, and multiaddr needs the multihash validator for its
`p2p` values. One unit for the whole package is too large to close at
once.

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W1.2, W2.1 | `Multiformats/Constants.lean` with the digest cap, `Base58`, the multibase registry with its generated table, and the strict `Multihash` with its function table, theorems, and `Codec` instances | the 1a milestones below pass, and the multibase table match test holds |
| 1b | 1a | `Cid` v0 and v1, with the `Codec` instances and the text forms | the 1b milestones below pass |
| 1c | 1b | `Multiaddr`: the generated protocol table with its match test, `parse?`/`toString`, `toByteArray`/`ofByteArray?`, the operations API, and the component and address caps | the 1c milestones below pass, and the root W2.3 row holds |

Unit 0 is done. Sub-units 1a, 1b, and 1c close root W2.3 together.

## Consumers

W5.1 (`libp2p/identity`) builds the peer id on multihash, a validated
multihash over the marshaled public key (root PLAN, W5.1). The CID
text forms give the peer id its string forms. W6.1 (ENR) maps ENR
entries to multiaddr, and `libp2p/host` (W5.6) carries multiaddrs
through the peerstore, and identify (W5.7) advertises them. The
surface freeze of the
sub-units is what lets those units start. The committed generated
table is part of the freeze, and it is the table W5.6 dials against.

## Test milestones

Behavior tests close the units. The suite follows the root test-runner
layout of W0.2, and the `-N1` pass is required. Each listed rejection
is a concrete case in the suite, so no milestone is vacuous.

Milestones for 1a:

- Multihash: the README vectors decode and re-encode
  (`multihash-examples.json`). The multihash decode splits its failures
  by kind: an unknown function code, a digest with trailing bytes past
  its declared length, and a digest over the cap report `malformed`; a
  digest cut below its declared length reports `truncated` through
  `framing`.
- Multibase: round-trips in both directions over the covered bases,
  from the four CSVs (`multibase-basic`, `multibase-case-insensitivity`,
  `multibase-leading-zero`, `multibase-two-leading-zeros`). A `decode?`
  on an unknown prefix character fails.
- Base58: each leading zero byte of a payload becomes one `1`
  character. The leading-zero CSVs pin the rule, and the base58btc
  encodings inside the multihash and peer-id vectors pin the
  arithmetic.
- The multibase table match test: the committed generated table equals
  `multibase.csv`.
- The generic harness closes `Multihash` (`base/bytes` docs, owned
  contracts 1 and 2).

Milestones for 1b:

- CID: the peer-id string examples of the peer-ids spec
  (`keys-peer-ids.json`) decode and re-encode. The `bafz...` CIDv1
  base32 form and the `QmYyQ...` base58btc form name the same bytes.
- Version mismatch rejection: a v0 payload that is not the sha2-256
  shape, and a v1 with a content codec outside the multicodec table,
  each fail through `Multiformats.Error`.
- The generic harness closes `Cid`.

Milestones for 1c:

- Text and binary round-trips over the table, from the go and js
  suites: `string-to-bytes`, `bytes-to-string`, `construct-succeeds`,
  `variants`, `normalize`, `round-trip`, `marshaler`.
- The strictness rejections, each concrete: a missing leading `/`
  (`tcp/1`), an empty segment (`/ip4//x`), a `_` digit separator
  (`/tcp/6_5_5_3_5`), and a leading-zero IPv4 octet
  (`/ip4/010.0.0.1`).
- Percent codecs over UTF-8: `%C3%A9` decodes to the two UTF-8 bytes
  of `é` and re-encodes to the same escapes (a package case; the
  `http-path` vectors pin the escape handling they carry).
- The operations: `encapsulate`, `decapsulate`, `decapsulateCode`,
  `get-value`, `equal`, `zone`, `dns`, `contains`, `unique-addrs`,
  `filter-addrs`, `split`, from the go and js operation vectors.
- The invalid corpora: `construct-fails`, `invalid`, `invalid-p2p` (a
  `p2p` value whose declared digest length mismatches), and the fuzz
  corpora `multiaddr-go-fuzz-bytes` and `multiaddr-go-fuzz-strings`.
  Decoding is total, and every accepted input round-trips.
- The table match test: the committed generated table equals
  `multiaddr-protocols.json`, the extraction of `protocols.csv`.
- The generic harness closes `Multiaddr`.

## Vector stance

The spike captured the multiformats vectors, and `VECTORS.lock` pins
their sources (ARCHITECTURE §6). They arrive on `main` through root
W0.3:

- `multihash-examples.json`: the multihash README vectors, sha1 and
  sha2-256 over hex, base32pad-upper, base58btc, and base64pad.
- The four multibase CSVs of `vendor/multibase/tests` (`basic.csv`,
  `case_insensitivity.csv`, `leading_zero.csv`,
  `two_leading_zeros.csv`, the upstream files the suite names
  `multibase-basic` and its siblings).
- `multiaddr-protocols.json`: the authoritative protocol table from
  `vendor/multiaddr/protocols.csv`.
- The multiaddr suites: 22 go files and 8 js files, including the fuzz
  corpora `multiaddr-go-fuzz-bytes.json` and
  `multiaddr-go-fuzz-strings.json`.

Two families have no captured vectors of their own. Base58 closes
through the multibase CSVs and the base58btc encodings inside the
multihash and peer-id vectors. CID closes through the peer-id string
examples in `keys-peer-ids.json` and the `p2p` cases of the multiaddr
suites. The spike captured no dedicated CID corpus. Where a family has
no vectors, the fixed tables and property tests of the milestones
close the unit, and the suite records the provenance
(ARCHITECTURE §6).

One gap: `VECTORS.lock` does not vendor the multicodec CSV, and the
spike wrote its multihash function table by hand. Unit 1a adds the
vendor entry through the W0.3 script, so the generated multicodec
slice meets §3.8.
