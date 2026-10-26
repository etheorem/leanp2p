# leanp2p: deferred findings and rejected findings

Findings from review that are not blocking. Each carries its file,
line, and the reviewer's wording. A deferred finding is either fixed in
a cleanup pass or dropped with a reason. A finding that changes scope
goes here too, under its task heading.

> Paths note: `crypto/cores` was renamed to `crypto/pure` at stage
> close-out; entries below that name `crypto/cores` read as
> `crypto/pure`.

## Pre-squash review, second round: pure rename and the etheorem origin split

Two more owner decisions amended the crypto group after the first
pre-squash review. Applied in commit `ae1b5d9`:

- Rename: `crypto/cores` is `crypto/pure` (namespace `CryptoPure`;
  a bare `Pure` namespace would collide with Lean's standard `Pure`
  typeclass).
- Origin split, per the owner's rule "if etheorem already binds it,
  use that one": secp256k1, ECDSA P-256, SHA-256, and keccak-256 route
  to the etheorem hazmat packages (`LeanHazmatSecp256k1`,
  `LeanHazmatP256`, `LeanHazmatSha256`, `LeanHazmatKeccak`); the
  backend keeps its own OpenSSL shim for Ed25519, X25519, RSA, SHA-1,
  SHA-512, HMAC, HKDF, ChaCha20-Poly1305, X.509, and randomness. The
  etheorem constraints are recorded at root §4.6: toolchain skew
  (v4.29.1 against v4.34), LGPL-3.0 with a CLA, monorepo-resident
  packages. Keccak-256 has no own fallback shim; a failed pin blocks
  W6.1. This entry supersedes the earlier keccak resolution
  (vendored C) and the first review's ETHEncodingLean keccak note.
  The owner then took the toolchain skew to etheorem: their monorepo
  will move its pin from v4.29.1 to this repo's v4.34, which retires
  the skew constraint above once it lands. The W3.2 build checks and
  the fallback rules stay in force until then.

## Pre-squash review: FFI-first and prior-art audit (stage close-out)

The owner asked for a review that the docs do not instruct
reimplementing, in Lean, things an FFI or an existing library covers.
Findings and resolutions:

- The crypto pairs had made the pure cores the production digests,
  against root §3.6's oracle reading. Resolved: backend production,
  cores as audited oracles (root `1c08751`; pairs `6df99fd`).
- SHA-1 stayed pure only for lack of a spike binding. Resolved: the
  binding joins W3.2, and the cross-check covers it.
- RLP: proven prior art exists in the Lean ecosystem. The owner
  named the source: the etheorem monorepo (`etheorem/etheorem`,
  LGPL-3.0, Lean v4.29.1), the Lean 4 consensus implementation this
  stack targets. Its RLP package is upstream work and not yet on its
  `main`; W6.1 tracks it, and the first look at `ETHEncodingLean`
  (MIT, proven RLP) was replaced by the owner's pick. Resolved: W6.1
  takes RLP from etheorem, wrapped behind the identity package's
  `Codec` surface, with the own-small-RLP fallback. The monorepo's
  `LeanHazmatKeccak` (keccak-tiny FFI) is recorded as the candidate
  future swap for the vendored-C keccak path. Resolved in root
  `1c08751` as amended, and the identity pair.
- Argument parsing: `leanprover/lean4-cli` adopted as first choice,
  hand-roll as recorded fallback (the `cli` pair).
- No action: the pure codecs (varint, protobuf, multiformats, yamux,
  the libp2p stack) have no library or FFI equivalent and exist for the
  proof strategy; the vendored-C keccak decision stands, with the
  library's pure Keccak256 recorded as a future facade swap.
- Resolved. The snappy binding's package home: `codec/snappy`, a
  standalone binding package in the codec group, wrapping upstream
  `google/snappy` (C++, runtime compiled out, the `LeanHazmatBn254`
  pattern). Recorded in root PLAN W6.2 and the protocols pair.
- Open, owner decisions: whether a pure-`Bool` verifier may carry a
  fault channel (§3.6).

## Cleanup pass (stage close-out)

Applied in commit 802305e. The batch collected the deferred doc fixes
from tasks 1 to 17. The two open questions that need an owner decision
stay at the bottom. The task 11 remoteMuxers question is dropped as
resolved: the negotiate pair (task 14) recorded the wire-based
selection decision. The applied batch:

- `packages/base/conc/docs/ARCHITECTURE.md`, the `withinDeadline`
  bullet: add §4.1 beside §5.4 (task 1).
- `packages/base/bytes/docs/ARCHITECTURE.md`: "a within-budget
  violation" rewording, and the §3.2 cite beside §5.2 on the
  act-on-the-result sentence (task 2).
- `packages/codec/multiformats/docs/PLAN.md`: name the upstream
  multibase CSV files once beside the captured JSON names, and cite
  W5.7 for identify in the consumers note (task 5).
- `packages/crypto/cores/docs/PLAN.md`: tighten the W5.3 consumer
  sentence; Noise reaches HMAC only inside HKDF (task 6).
- `packages/crypto/backend/docs/PLAN.md`: the `keys-peer-ids.json`
  stance names the W0.3 extractor emission as the raw-fields mechanism,
  as `keys-go-libp2p.json` already does (task 7).
- `packages/net/streams/docs/ARCHITECTURE.md`: the caps decision names
  the security constants module by its real name
  (`Libp2p/Security/Constants.lean`), not the §3.8 shorthand (task 12).
- `packages/libp2p/security/docs/ARCHITECTURE.md` contract 4 and
  `PLAN.md`: align with the negotiate pair's refinement; the host
  supplies the expectation, the upgrader compares (task 14).
- `packages/libp2p/host/docs/PLAN.md`: the unit 1a registry milestone
  gains the clause that the checks run as pure functions over the
  registry, with no connection in the loop (task 15).

## per-package docs, task 1: base/conc

- Deferred. `packages/base/conc/docs/ARCHITECTURE.md:50`, the
  `withinDeadline` bullet cites §5.4 alone; its mechanism sentence is
  §4.1 verbatim. Adding "§4.1; §5.4" would match the dual-cite style of
  the `Chan` and `select` rows. Non-blocking; the citation stands.
- Rejected. None this task.

## per-package docs, task 2: base/bytes

- Deferred. `packages/base/bytes/docs/ARCHITECTURE.md:69`,
  "a within-budget violation" could first parse as "a violation of the
  budget"; the named example pins the meaning. Wording polish only.
- Deferred. `packages/base/bytes/docs/ARCHITECTURE.md:64`, the
  sentence cites §5.2 for both halves of the act-on-the-result
  statement; the waiting half follows from §3.2. Defensible; a
  dual cite would be tighter.
- Rejected. None this task.

## per-package docs, task 3: codec/varint

- Deferred. None.
- Rejected. None this task. The review's blocking finding (the
  round-trip law was false for representable values) was fixed by a
  lead decision: `UVarint` is a proof-carrying newtype per root
  ARCHITECTURE §3.7, so the `base/bytes` class law stays unchanged.

## Incident: `codec/proto` wire order and the `LawfulCodec Fields` law

Found in per-package docs, task 4. Three root statements do not hold
together for `Fields`:

- ARCHITECTURE §4.5: "The encoding is deterministic by construction
  (tag order, minimal varints)."
- ARCHITECTURE §3.2 lists `Pb.Fields` among the `Codec` instances, and
  §6 lists protobuf among the codecs that prove round-trip "as
  `LawfulCodec` instances".
- ARCHITECTURE §3.7: "`Fields := List (Nat × Value)`" is the stated
  `abbrev` with no invariant, so the varint resolution (carry the fact
  in the type) is closed here.

If the encoder sorts by tag (the §4.5 literal reading), a decoded
`Fields` re-encodes to the sorted form, so `decode? (encode fs) = fs`
is false for unsorted input and the `LawfulCodec` law cannot be proved.
The captured evidence points the other way too: the spike's
`Tests/vectors/protobuf-messages.json` Identify case carries bytes in
emit order 5, 6, 1, 2, 2, 4, 3, 3, and the spike's `Fields.wf` plus
`decode_encode` show the reference kept wire order and carried the
well-formedness hypothesis on the theorem. Field numbers also need a
bound (the spike uses `< 2^59`, budget-derived), and a raw `Nat` field
number has none, so some home for that fact is needed either way.

Pinned versions: root docs at commit 6687abc; spike branch as of
October 2026 (`LeanP2P/Crypto/Pb.lean`, `Tests/vectors/protobuf-messages.json`).

Resolved. The owner picked: the wire layer preserves input order, and
`Fields` carries the budget fact in the type. The root amendments
landed first (commit 0cabf36), and the package docs follow them.

## per-package docs, task 4: codec/proto

- Deferred. None.
- Rejected. None this task. The first draft followed the old §4.5
  parenthetical literally; the owner decided both questions above, and
  the rewrite implements them.

## per-package docs, task 5: codec/multiformats

- Deferred. `packages/codec/multiformats/docs/PLAN.md`, the 1a
  milestone names the multibase families by their captured JSON names
  while the vector stance names the upstream CSVs; one cross-reference
  would remove the mapping step for a new reader.
- Deferred. `packages/codec/multiformats/docs/PLAN.md`, the consumers
  note attributes identify to W5.6; the root plan puts identify in
  W5.7. Cite W5.7 for identify.
- Open item, cross-package. `VECTORS.lock` does not vendor the
  multicodec CSV, and the spike hand-wrote its multihash function
  table. Root §3.8 says the multicodec table comes from the vendored
  CSV. The package PLAN assigns the vendor entry to unit 1a through
  the W0.3 script; keep the assignment visible when W0.3 lands.
- Rejected. None this task.

## per-package docs, task 6: crypto/cores

- Deferred. `packages/crypto/cores/docs/PLAN.md`, the W5.3 consumer
  sentence says Noise consumes HMAC through the facade; the spike calls
  HMAC only inside HKDF. True transitively; tighten if the file is
  edited again.
- Rejected. None this task.

## per-package docs, task 7: crypto/backend

- Deferred. `packages/crypto/backend/docs/PLAN.md`, the
  `keys-peer-ids.json` stance says the raw key material feeds the
  suites without naming the mechanism; one clause pointing at the same
  W0.3 extractor emission as `keys-go-libp2p.json` would close it.
- Open question, root-level. §3.6 fixes pure verifier bindings as
  `Bool`, so a shim fault and an invalid signature read the same to the
  caller. The pair follows the root faithfully. Decide at the root
  whether a verifier may return `Except CryptoError Bool`.
- Rejected. None this task.

## per-package docs, task 8: net/streams

- Deferred. None.
- Rejected. None this task.

## Incident: ENR signature needs keccak-256, which no unit provides

Found in per-package docs, task 10. Root PLAN W6.1 assigns the ENR
codec to `libp2p/identity`: "RLP codec (small, pure) + ENR
encode/decode + peer-id/multiaddr mapping". The ENR canonical identity
scheme (`v4`, EIP-778) signs the keccak-256 digest of the record
content with secp256k1. The repository has no keccak-256: the backend
binds none, the cores implement none, and no root unit adds one
(OpenSSL 3 offers SHA3-256, whose padding differs from keccak-256, so
the existing shim cannot serve). The identity pair's first draft said
"`Enr` verifies the signature through the facade", which is
unimplementable as the units stand. A second interaction: the backend
verifier accepts low-S secp256k1 signatures only (§4.6), while `v4`
signatures carry a recovery byte and do not promise low-S. The ENR and
discv5 spec texts are also not vendored under `vendor/specs` on the
spike branch, so the source must be named and the fixture provenance
recorded whatever the decision.

Pinned versions: root docs at commit c78348c; spike branch
`vendor/specs` (no ENR/discovery document; only `mdns.md` under
`discovery/`).

Resolved. The owner picked FFI-first for keccak-256: a small C source
vendored into the crypto/backend shim, with room for further C
dependencies under the FFI-first rule (CLAUDE.md "Dependencies" as of
commit 9bb3a28). RLP keeps its root-assigned pure path (root PLAN W6.1:
"small, pure"). The low-S conflict yields ENR-local: the identity
module verifies over the recovery path behind its own function, the one
documented exception to the §4.6 rule. Root amendments landed in
ddf90cb (keccak-256 in W3.2 and W6.1) and 9bb3a28 (the C-dependency
rule); the backend pair followed in 658227e and cdd71b8.

## per-package docs, task 10: libp2p/identity

- Deferred. None.
- Rejected. None this task. The first draft verified ENR signatures
  "through the facade" with no keccak anywhere; the owner's decisions
  above resolved it, and the pair names EIP-778 and the discv5 ENR
  section as its sources, with the vendoring step as unit 2's first
  work.

## per-package docs, task 9: net/yamux

- Deferred. None.
- Rejected. None this task.

## per-package docs, task 11: libp2p/core

- Deferred. None.
- Open question, for the security and negotiate pairs (W5.3, W5.5).
  The spike's `SecureConn.remoteMuxers` carried the muxer list the
  Noise extensions advertise, and go-style muxer selection consumed it
  (`Upgrade.matchMuxers`). The core pair leaves the field out; W5.3
  owns the handshake extensions, and W5.5 records whether muxer
  selection reads them or negotiates on the wire. Decide when those
  pairs land.
- Rejected. None this task.

## per-package docs, task 12: libp2p/security

- Deferred. `packages/net/streams/docs/ARCHITECTURE.md`, the dependency
  bullet cites this package's constants module by the §3.8 shorthand
  `Noise.Constants`; the real name is `Libp2p/Security/Constants.lean`.
  Harmless shorthand; align it in the cleanup pass.
- Rejected. None this task.

## per-package docs, task 13: libp2p/mux

- Deferred. None.
- Rejected. None this task.

## per-package docs, task 14: libp2p/negotiate

- Deferred. Follow-up touch to the security pair: its contract 4 and
  PLAN say "the host compares" the completed `remotePeer`; the
  negotiate pair records the refinement (the host supplies the
  expectation, the upgrader compares). Align the security wording in
  the cleanup pass.
- Rejected. None this task.

## per-package docs, task 15: libp2p/host

- Deferred. `packages/libp2p/host/docs/PLAN.md`, the unit 1a
  registry milestone leans on served-stream wording while 1a lands
  without W5.5; the checks run as pure functions over the registry,
  and one clarifying clause would make that explicit.
- Rejected. None this task.

## per-package docs, task 16: libp2p/protocols

- Deferred. None.
- Rejected. None this task. The error-inductive contract was decided
  by the owner (one per protocol) and the root amendment landed as
  99d0cc4.

## Open questions

None. Both questions this stage carried are resolved:

- The snappy binding's home: `codec/snappy` (root PLAN W6.2; the
  protocols pair records it).
- The pure-`Bool` verifier fault channel (§3.6): the owner picked the
  documented fold. Verifier bindings return `Bool`; `false` covers a
  malformed input and a shim fault alike, fail-closed, and each
  verifier docstring states the fold. Recorded in the backend pair;
  etheorem's verifiers follow the same pattern.

## W0 cleanup batch (stage close-out)

Applied batch: the four W0.1 docstring findings and the W0.2c
`timeout-minutes` finding. The review added one more split (the Crypto
roles sentence), applied with the batch. Dropped, with reasons:

- The "concurrency floor" phrase survives in
  `packages/base/conc/docs/ARCHITECTURE.md:3` ("byte floor" in the
  bytes pair likewise). Those package docs predate W0, passed the docs
  stage with that wording, and the W0.1 finding was scoped to the new
  root module. Align the term only if the package doc is edited again.
- The within-group lint rules, the `vendor/` move, the CI provenance
  diff, and the multicodec CSV vendor entry are unit work with owners
  (W1.1/W1.2, a later vector unit, `codec/multiformats` 1a), recorded
  in their sections above.

## W0.1: the lake skeleton

Reviewer verdict: clean, nothing blocking. Four deferred docstring
findings, for the stage-close cleanup batch:

- Deferred. `packages/base/conc/Conc.lean:4`, "the concurrency floor of
  the stack" coins a term; §4.1's own title is "concurrency
  primitives", and one word carries one meaning.
- Deferred. `packages/codec/snappy/Snappy.lean:4-5`, unit W6.2 appears
  in two consecutive sentences; cut one statement of it.
- Deferred. `packages/cli/Cli.lean:7`, "the executables arrive with
  W5.8" covers all three binaries the docstring names, but the
  interop harness arrives with W5.9. The sentence also joins two
  independent claims.
- Deferred. `packages/crypto/Crypto.lean:4-5`, "one import surface over
  the pure copies and the backend bindings" names two of the three legs
  §3.6 enumerates (the etheorem packages are the third) and reads the
  pure copies as a production leg; §4.6 makes the backend the
  production path and the pure copies the audited oracles.

Decision of record, from the owner's pointer at the etheorem repo: the
globs question. The etheorem incident `8d40ef2` (fix(sizzlean): resolve
the module glob against the package directory) is the same bug class:
a glob read a directory that did not resolve under the workspace root,
the read failed, and the library silently built only what its root
re-exports. Our shape takes the other half of the etheorem answer, the
`LeanRlp/lakefile.toml` form: no `globs` line, so the Lake default
(`roots.map Glob.one`) applies, and a unit widens its glob to `X.*`
only in the commit that adds the first submodule, because `X.*` reads
the `X/` directory and the load fails while it does not exist. The
silent-omission guard is the docs rule that every root re-exports its
public submodules. Carried note for the first `lakefile.lean` in this
repo (the crypto/backend C target is the likely first): a lakefile
that computes globs must resolve paths against `__dir__` and treat an
unreadable directory as a configuration error, per `8d40ef2`.

Rejected, with reasons:

- `lakefile.toml` header comment, first sentence carries two
  coordinated claims. Kept: one line, reads clean.
- Untracked `mb` symlink at the repo root. Outside the diff; the
  owner's local file, untouched.

## W0 deferred closure (post stage close-out)

The owner directed the open deferrals closed. Applied in two commits
(`ci: W0 (deferred)`, `test: W0 (deferred)`):

- Applied. The W0.2a within-group deferral: rule 3 of the lint encodes
  the downward orders of §2 for net, codec, crypto, and libp2p, with
  the §3.1 carve-outs (negotiate and host import core and no
  implementation). An unknown leaf fails loud. Decision of record,
  snappy's rank: §2 states an order and names no snappy edge, and a
  rank table states an order, so snappy sits at the codec bottom
  (rank 1, beside varint): a snappy file imports no codec leaf, and
  higher codec leaves may import it as headroom. The docs win on a
  conflict; a within-codec snappy edge needs a §2 row first.
- Applied. The W0.3 vendor deferral: `vendor/` (eleven pinned copies)
  and `scripts/vendor-pull.sh` moved from the spike branch. The
  extractor rerun on `main` is byte-identical over the whole corpus
  (proven twice), and CI runs the provenance gate. Two deltas from
  the spike's copies, both recorded: `--verify` exits nonzero on
  MISSING, PIN-MISMATCH, or BAD (the spike's printed and exited 0),
  and the no-arg fetch mode drops a `set -u` abort the spike carried.
  The CI corpus gate uses `git status --porcelain` rather than the
  spike's `git diff --exit-code`, so an untracked corpus file fails
  too.
- Applied. The suite byte-exactness deferral closes with the gate:
  the suite pins provenance and three shapes, and the gate pins the
  byte-exact regeneration.

Still open, with owners:

- The multicodec CSV vendor entry: `codec/multiformats` unit 1a, per
  the per-package docs record; the extractor and the vendor path now
  sit ready for it.
- The `public import` caveat in the lint: reruns on a toolchain bump.

Closed since:

- CI observability. The repository pushes to `etheorem/leanp2p`, and
  the first CI run is green: all five gates, the vendor verify
  included.

## W0.2b and W0.2c: the test runner and the CI workflow

W0.2b reviewed clean on the first round; no findings. W0.2c reviewed
clean with two deferred findings:

- Deferred. `.github/workflows/ci.yml`, the job sets no
  `timeout-minutes`. A deadlocked suite, the exact failure the `-N1`
  criterion polices, burns the 360-minute default before CI fails. The
  spike's CI carries the same gap. Fix in the cleanup pass with a cap
  (60 minutes is the reviewer's number).
- Deferred. CI green is unverified: the repo has no git remote, so no
  run has executed. The W0.2 evidence is command parity with the local
  gates plus a YAML parse. Revisit when a remote exists.

Rejected, with reasons:

- The bare `on:` key parses as boolean `true` under YAML 1.1 readers.
  GitHub's parser accepts it and the spike uses the same shape; quoting
  it serves third-party tooling only.
- Explicit `build: true` / `test: true` restate lean-action's defaults.
  Kept: the spike does the same, and the explicit form documents
  command parity.

## W0.3: the vector infrastructure

Decision of record: the task's literal provenance spec (every file
carries `repo`/`commit`/`path` strings and `extractedBy` exactly
`scripts/extract-vectors.py`) is false against the frozen corpus, and
the corpus is byte-frozen, so the spec yielded. Four files are
go-libp2p captures (`scripts/capture-vectors.go`), two RFC files embed
the extractor and carry no `commit`, `protobuf-messages.json` carries
no `path`. The suite pins the invariant that holds corpus-wide:
`_provenance` with `repo`, `upstreamTest`, and `extractedBy` strings,
`extractedBy` containing `scripts/`, and the module docstring
documents the three kinds. The lead verified the invariant over all
50 files.

- Closed post stage close-out. `vendor/` and `scripts/vendor-pull.sh`
  moved to `main`, the extractor rerun is byte-identical, and CI runs
  the provenance gate; see the W0 deferred closure section.
- Closed post stage close-out. The CI gate pins byte-exact
  regeneration over the whole corpus.
- Deferred, carried. The multicodec CSV vendor entry stays out of
  `VECTORS.lock`: per-package docs task 5 assigns it to
  `codec/multiformats` unit 1a, through the W0.3 script. Kept visible
  here so the assignment does not get lost.

Rejected, with reasons:

- The untracked `mb` symlink. The owner's local file; commits stage by
  name, never `git add .`.

## W0.2a: the import lint

Reviewer verdict after two rounds: two blocking findings, fixed in the
same task. The fixed round also applied two comment corrections the
reviewer had rejected; the lead overrode both rejections because a
false or misleading comment in a gate script is a defect of its own.

- Deferred. `scripts/lint-imports.sh` (rule 1): `public import` escapes
  the grep pattern once a toolchain compiles it. On the v4.34.0 pin it
  parses but cannot compile (`module` support is missing), so the hole
  is closed today; the caveat lives as a comment in the script and the
  check reruns on a toolchain bump.
- Closed post stage close-out. The within-group downward rules and
  the "negotiate and host import core and no implementation" rule
  (§3.1) landed as rule 3 of the lint; see the W0 deferred closure
  section. No unit wait remains.

Rejected, with reasons:

- CR strip placement (before the `case`): verified correct; a CRLF
  `Conc` resolves to base, not to the external branch.
- `set -e` interaction of the directory checks: verified safe, explicit
  `exit 1` inside the `if`, before both loops.
- The widened pattern can match an `import` inside a block comment.
  True, and it fails loud instead of silent; the whole-file scan stays.
