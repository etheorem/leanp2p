# leanp2p: Agent Notes

A Lean 4 implementation of libp2p. The target in priority order is the
Ethereum consensus layer: a node speaks `tcp + /noise + /yamux`,
negotiates with multistream-select, answers identify, and carries the
consensus traffic (req/resp in `ssz_sn` framing, gossipsub v1.1). The
stack is built from small packages under strict dependency rules, and
each package owns contracts that the spike proved out. Crypto and other
mature foreign implementations are consumed FFI first, through small C
shims behind Lean interfaces; a native Lean replacement may follow,
behind the same interface.

**Status: bootstrap.** W0 landed on this branch (`main`): the package
scaffold, the import lint, the test runner, and the vector
infrastructure. Packages land per `docs/PLAN.md`. The `spike` branch
of this same repository
holds the reference implementation: working wire formats, the captured
go-libp2p vector suites (`VECTORS.lock`), the vendored libp2p and
multiformats specs (`vendor/specs`), and a 3148-check suite that also
passes under `+RTS -N1`. When you implement a unit, read the matching
spike module first; the documents tell you where the spike is not to be
followed.

The remote is `etheorem/leanp2p` (GitHub, `origin`). Do not guess
repository URLs beyond it for `gh` commands or PR links.

## Principles

These have standard names, and good Lean libraries already follow them.
They appear below as concrete conventions; this section is the *why*, so
edge cases can be judged on principle instead of pattern-matching.
[`docs/PRINCIPLES.md`](docs/PRINCIPLES.md) explains each one in detail,
with the incidents that earned it.

- **Literate by default.** libp2p-in-Lean sits at a small intersection:
  most readers know one side of it. Comments should teach the spec and
  the language as the file unfolds. Use module docstrings (`/-! … -/`)
  to frame each file against the spec section it implements, declaration
  docstrings (`/-- … -/`) for the *why* of every public definition, and
  `example` blocks for usage the typechecker keeps honest. Annotate
  non-obvious Lean idioms the first time they appear in a module. Same
  for wire-format details a Lean reader will not recognize (varint
  boundaries, framing caps, flag bits, nonce layout).

  Explain non-obvious *inferences* with the same rigor. Lean infers
  types, instances, motives, and most of it is unremarkable, but some of
  it decides what the code means: a coercion that forces defeq
  reduction, a pattern match that relies on an unfolded constructor, a
  typeclass instance picked by a phantom tag. When the inference is the
  thing a reader needs to follow, name what Lean inferred and *why* in a
  one-line comment. Type-annotate intermediate bindings whose type
  changes the meaning of the code after them; leave inference alone
  where it reads cleanly.

- **Single Responsibility (SRP).** Each file, namespace, and definition
  does one thing. A muxer session that parses frames, manages flow
  control, and owns timers in one module is a smell at module scale,
  the same way a 1000-line function is a smell at function scale.

- **Open/Closed (OCP).** Extend by adding code. A new transport, security
  protocol, or muxer lands as a new value of the existing seam
  (`Transport`, `SecurityProtocol`, `Muxer`). If adding one requires
  editing the upgrader, the seam is wrong.

- **Dependency Inversion (DIP).** Code against the seams, not the
  concrete transport. Tests for a protocol should run over the in-memory
  sim transport; only the transport suite needs real TCP.

- **DRY: one canonical home per fact.** A frame layout is defined once
  in the proved codec, and the IO shell imports it. Protocol constants
  (length caps, window sizes, timeouts, protocol ids) live in one module
  and are imported, never re-typed. Two copies of a constant drift; the
  spike paid for this lesson more than once.

- **No hidden coupling.** Lean has no mutable globals, but `set_option`
  and `open` at file scope leak into every importer. Keep them tight to
  the section that needs them. Do not rely on import order for
  correctness.

- **Configure, don't integrate.** Keep package metadata declarative
  (`lakefile.toml`). `lakefile.lean` is permitted only for targets the
  declarative form cannot express; the C shim build in `crypto/backend`
  is the standing example. Keep it small.

- **Spec is the source of truth.** Behavior comes from the libp2p specs
  (vendored on the spike branch under `vendor/specs`), the multiformats
  specs, and the captured vectors. When another implementation disagrees
  with the spec, the spec wins, and we record the discrepancy. When two
  upstream implementations disagree with each other, the chosen side is
  a documented decision; the spike records several of these (peer-id
  print form, percent codecs, garlic padding rules).

- **Lean on Lean.** Prefer what the language gives you: `deriving`
  instances, `simp` lemmas, `Decidable` + `decide` for finite goals,
  structural recursion over `partial def`. Reach for `batteries` before
  re-implementing a list utility. Do not pull in `mathlib`; nothing here
  needs it.

- **Strict checking is a force multiplier.** Prefer
  `set_option autoImplicit false` per file. Treat `sorry`, unused
  variables, and linter warnings as build failures in spirit even before
  CI enforces them. The cost of strictness is paid once; the cost of a
  missed implicit is paid forever.

- **Stringly-typed is a smell.** Protocol ids, multicodecs, and frame
  flag kinds get named constants or inductives in one module, not raw
  strings and magic numbers scattered through the logic. If behavior
  decides by comparing strings, the type is asking to be promoted.

- **Concurrency discipline.** Three rules, binding everywhere: never
  cancel a task, wake it by closing what it parks on; every task has an
  owner that joins it; shared state changes atomically through
  `OnceRef.update`, never get-then-set on a bare `IO.Ref`. The contracts
  live in ARCHITECTURE.md §4.1 and §5; treat a violation in review as a
  build failure in spirit.

- **Bounded inputs.** Every length-prefixed read is capped before
  allocation, and an over-long varint is a protocol error. This is
  ARCHITECTURE.md §5.1. A new framing layer without a cap does not get
  merged.

- **FFI first, Lean later.** A primitive with a mature native
  implementation gets a C shim behind a Lean interface; a pure-Lean
  implementation follows only where it pays, behind the same interface.
  Callers depend on the Lean interface, never on the FFI.

These map onto the usual references: Fowler's *Refactoring* (smells),
Hunt & Thomas's *The Pragmatic Programmer* (DRY, orthogonality), Martin's
*Clean Code* / *Clean Architecture* (SRP, DIP), and Meyer's *Object-Oriented
Software Construction* (Open/Closed), adapted to a dependently typed,
proof-carrying setting where typeclasses and structure values do most of
the work that interfaces and patterns do elsewhere.

## Layout

Two branches share this checkout:

- **`main`** (this branch): the implementation. The scaffold landed
  with W0; packages land per `docs/PLAN.md`.
- **`spike`**: the reference implementation, complete through phase 5.
  Its tree: `LeanP2P/` (the whole stack under one namespace), `Tests/`
  (one suite module per upstream file), `c/p2pcrypto.c` (the OpenSSL
  shim), `scripts/` (vector extraction, go interop), `vendor/` (pinned
  specs and upstream sources), `VECTORS.lock`, `VECTOR_TEST_PLAN.md`,
  `README.md` (the spike's own record).

The `main` tree once W0.1 lands:

```
packages/
  base/                        foundations, no wire-format knowledge
    conc/                      Chan, Pipe, TaskSet, OnceRef, withinDeadline
    bytes/                     List-Nat byte model <-> ByteArray/String
  codec/                       encodings
    varint/                    unsigned varint
    multiformats/              multihash, multibase, base58, cid, multiaddr
    proto/                     protobuf wire codec
  crypto/
    Crypto.lean                the facade every caller imports
    pure/                      sha256/sha512/sha1/hmac/hkdf, pure and proved
    backend/                   OpenSSL 3 C shim + @[extern] bindings
  net/
    streams/                   Connection, BufReader, Framing, Stream, tcp
    yamux/                     the stream muxer
  libp2p/
    identity/                  keys, peer ids
    core/                      ProtocolId, Core.Error, the libp2p seam types
    security/                  Noise XX as a SecurityProtocol value
    mux/                       Muxer values: yamux, mplex
    negotiate/                 multistream-select, upgrader
    host/                      host, peerstore, dedup, deadlines
    protocols/                 identify, ping
  cli/                         demo node, ping node, interop harness
docs/                          ARCHITECTURE.md, PLAN.md (repo-wide)
scripts/                       vector extraction and capture (W0.3)
```

Design docs live next to the code they describe. The repo carries
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) (binding on substance:
contracts, dependency rules, priorities) and
[`docs/PLAN.md`](docs/PLAN.md) (binding on order: units, dependencies,
gates). Each package adds `docs/ARCHITECTURE.md` and `docs/PLAN.md` as
its first work unit; they refine the root documents and never contradict
them. This file (CLAUDE.md) is binding on style, conventions, and
discipline across all packages; when those overlap with architectural
decisions, the relevant ARCHITECTURE.md wins on substance and CLAUDE.md
wins on form.

## Conventions

- **Module names mirror file paths.** `Conc/Chan.lean` gives
  `import Conc.Chan`. Package root modules are PascalCase (`Conc`,
  `Bytes`, `Varint`, `Multiformats`, `Proto`, `Streams`, `Yamux`); the
  group directories are lowercase as in the tree above.
- **`import` must be the first thing in a file**, before any `/-! … -/`
  module docstring, before any `set_option`. Lean rejects imports placed
  later.
- **Library root re-exports.** New public submodules go into the library
  root (`Conc.lean`, `Streams.lean`, …) as one `import` line each.
  Internal-only helpers do not need re-export.
- **Naming:** types, structures, inductives, namespaces → `PascalCase`;
  defs, theorems, fields, variables → `lowerCamelCase`.
- **Namespacing.** Wrap declarations in the package's namespace
  (`namespace Conc … end Conc`, `namespace Streams …`); `libp2p`
  subpackages nest under `Libp2p` (`Libp2p.Identity`, `Libp2p.Security`,
  …). The public API is namespaced, never bare.
- **Doc comments:** `/-- … -/` on declarations, `/-! … -/` for
  module-level prose. Skip comments that restate the code.
- **No committed `#eval` / `#check` / `#print`.** Use
  `example : … := by …` or `#guard` for assertions the build should
  enforce.
- **Tactic style:** prefer structured `by` blocks; use `· …` bullets
  rather than long `;`-chains. `decide` is fine for finite goals;
  `native_decide` also works but trusts the compiler, say so when you
  use it.
- **`partial def` only when termination really cannot be shown.** The IO
  read loops are the standing precedent; the spike marks them `partial`
  and says why in the module doc. Prefer structural recursion or
  `termination_by` + `decreasing_by` for everything else.
- **Function-body readability.** Paragraph a long definition by phase,
  name the intermediates, and split when a definition stops reading top
  to bottom. The reviewed spike modules (for example `Conn/Yamux.lean`
  and `Conn/Noise.lean` on the spike branch) show the standard.

### Proofs and tests

Pick the tool by what the goal needs. The spike's split, kept:

1. **Pure codec theorems.** The verified cores (varint, protobuf,
   framing, yamux header) are stated over the `List Nat` byte model and
   closed by `rfl` / `simp` / `omega`. Keep them total; no `sorry`.
2. **Production paths.** The `ByteArray` decoders that actually run are
   pinned to the proved model by fuzz property tests
   (`decodeBinB b = decodeBin (toNatList b)`), so proof view and wire
   view cannot drift.
3. **FFI behavior.** OpenSSL results are checked through the vector
   suites, not through the kernel. Do not try to `decide` an
   `@[extern]` result; `native_decide` over compiled data is acceptable
   for finite goals, and it cites a compiler axiom when used.

Default rule: theorems live on the pure cores; IO behavior is pinned by
vectors and property tests. A theorem about an FFI return value is
almost always in the wrong place.

## Workflow

After W0 lands (see `docs/PLAN.md`):

```bash
lake build              # Build everything. Run after every change.
lake build Conc.Chan    # Build a single module.
lake test               # The vector suites; must pass, also under +RTS -N1.
lake env lean --run …   # Run a Lean script with the package env.
```

Until W0 lands, this branch has no build. Implement W0 first; do not
write package code before the scaffold, the lint, and the vector
infrastructure exist.

## Dependencies

One pinned toolchain (v4.34; the spike's `lean-toolchain` is the
reference). Use a C dependency where a mature implementation exists.
Bind each one through a small C shim behind a Lean interface
(ARCHITECTURE.md §4 preamble); OpenSSL 3 for `crypto/backend` is the
current one. Adding a Lean dependency: add the require block, run
`lake update`, commit `lake-manifest.json`, and pin the dependency's
git rev. Reach for `batteries` before anything heavier; `mathlib` stays
out. Go and Rust tooling is test-only, confined to the harness, and
never on a shipped or proof path.

## Scope

The libp2p specs (vendored on the spike branch under `vendor/specs`) and
the multiformats specs govern behavior. When the code disagrees with a
spec, the spec wins, and we record the discrepancy rather than paper
over it.

In scope for v1 (P0 in ARCHITECTURE.md §8): tcp transport, Noise XX,
yamux, multistream-select, identity (keys, peer id), identify, host and
upgrader, req/resp (`ssz_sn`), gossipsub v1.1, and the ENR codec.
Deferred to seams only: TLS and the X.509 extension, mplex beyond the
interface, QUIC/WebTransport, kad-dht, mDNS, relay and circuit, hole
punching, WebSockets, WebRTC, pnet, peer records.

## Don'ts

- Don't edit `.lake/` or `lake-manifest.json` by hand.
- Don't bump `lean-toolchain` casually; it cascades through every
  package.
- Don't add an AI session tag or an AI `Co-authored-by` trailer to a
  commit message. The `AI co-author guard` workflow fails on both.
- Don't untick or delete the license acceptance line in a pull request
  description. The `License acceptance guard` workflow fails without it.
- Don't leave `sorry` in committed code without a `TODO` and a tracking
  note.
- Don't import libp2p from the packages below it; the import lint
  exists, keep it green.
- Don't read past a length prefix without a cap; every framing read is
  bounded before allocation (ARCHITECTURE.md §5.1).
- Don't write constant-time primitives in Lean; bind them (§4.6).
- Don't cancel tasks; wake them by closing what they park on (§4.1).
- Don't hand a handler a raw stream when negotiation produced buffered
  bytes; hand the leftovers on (§5.6).

## Writing Style & Structural Constraints

Covers every word you write for this project: comments in code,
documentation files, commit messages, GitHub issues and PRs, and replies
to the user in conversation. One standard everywhere, so prose does not
change register when it moves from a chat reply into a docstring.

### Simplified Technical English

Write Simplified Technical English. The working core of it:

- **One word, one meaning.** Pick a term for a thing and keep it.
  `peer id`, `muxer`, `half-close`, `deadline`, `window update` mean
  what the specs and the ARCHITECTURE docs say they mean, in every file.
  Do not reach for a synonym to avoid repeating a word.
- **One instruction per sentence.** Split a sentence that carries two
  independent claims.
- **Short sentences.** Twenty words is a good limit for a statement, and
  twenty-five for a description. Longer needs a reason.
- **Say who acts.** Name the subject that performs the action: "the
  frame pump dispatches the header", "the upgrader threads the reader".
- **Keep the articles.** Write "the frame pump", not "frame pump".
- **No noun stacks.** Three nouns in a row is the limit. Break
  "receive window credit return path" into a phrase with a preposition.

### Orwell's six rules

From *Politics and the English Language*, and they outrank any stylistic
instinct to the contrary:

1. Never use a metaphor, simile, or other figure of speech which you are
   used to seeing in print.
2. Never use a long word where a short one will do.
3. If it is possible to cut a word out, always cut it out.
4. Never use the passive where you can use the active.
5. Never use a foreign phrase, a scientific word, or a jargon word if
   you can think of an everyday English equivalent.
6. Break any of these rules sooner than say anything outright barbarous.

Rule 5 does not ban this project's vocabulary. Four domains meet here,
and each brings terms that no everyday word replaces:

- **Lean and type theory:** `defeq`, `whnf`, `motive`, `elaborator`,
  `reducible`, `opaque`, `typeclass`, `instance`, `coercion`, `universe`,
  `olean`, `axiom`, `kernel`, `termination_by`, `Task`, `Promise`,
  `Mutex`, `decide`, `native_decide`.
- **libp2p and networking:** `peer id`, `multiaddr`, `muxer`, `stream`,
  `half-close`, `framing`, `upgrade`, `multistream-select`, `Noise`,
  `transport`, `listener`, `dedup`, `deadline`, `GoAway`, `SYN`, `FIN`,
  `RST`, `window update`, `req/resp`, `gossipsub`, `mesh`, `scoring`,
  `ENR`.
- **Multiformats and encodings:** `varint`, `LEB128`, `multihash`,
  `multibase`, `multicodec`, `base58`, `CID`, `percent-encoding`,
  `protobuf`, `wire type`, `tag`.
- **Crypto and FFI:** `FFI`, `@[extern]`, `shim`, `borrowed`, `@&`,
  `boxed`, `unboxed`, `endianness`, `AEAD`, `seal`, `open`, `nonce`,
  `tag`, `X.509`, `SPKI`, `DER`, `low-S`, `constant-time`, `TCB`.

The repo's own terms of art stay as well, and they mean one thing each:
`seam` (a structure value a layer calls out through), `class` (a
typeclass for behavior the type fixes), `core` (a pure transition
function), `loop` (the one task that drives a core), `group`, `track`,
`unit`, `wave`, `gate`, `vector`, `fixture`, `conformance`,
`differential test`, `oracle`, `deadline`, `pending` (a connection
still inside its unauthenticated phase).

Rule 5 bans the jargon that replaces a plain word for no gain. Examples,
and the list is open: `ride along`, `load-bearing`, `sanctioned` (write
"allowed"), `verdict` (write "answer"), `plumbing`, `baked in`,
`escape hatch`, `under the hood`, `blast radius`, `paper over`,
`canary`. It also bans borrowed Latin (`inter alia`, `a priori`,
`vice versa`) where English does the job.

Rule 6 is the only exemption, and it is narrow. Clarity outranks the
other five. A passive is right when the actor is unknown or beside the
point ("the promise is dropped by the runtime" is worse than "the
runtime drops the promise", but "the promise was already resolved" is
fine).

### Sentence Construction (Hard Enforcement)

- **No contrastive negation or antithesis.** Never use patterns like
  "It's not about X, it's about Y" or "X, not Y, not Z." State the
  positive reality directly and cleanly, without defensive framing.

### Punctuation & Sentence Structure

- **No em-dashes for subphrases.** Never use em-dashes (—) or hyphens
  (-, --) to set off parenthetical thoughts, interruptions, or
  subphrases.
- **Use commas instead.** Set off descriptive tangents or subphrases
  with commas (apposition).
  - Bad: "The strategy—though risky—yielded massive results."
  - Good: "The strategy, though risky, yielded massive results."
- **Keep sentences clean.** If a subphrase needs more than two commas to
  execute, split it into two distinct, clean sentences instead of one
  complex sentence.

### Structural Rhythm & Voice

- **Vary sentence length.** Alternate between short, punchy sentences
  (under 5 words) and longer, flowing ones. Never write three sentences
  of similar length in a row.
- **No statement-explanation loops.** Do not state a fact or opinion and
  then spend the next sentence explaining, justifying, or restating it
  in other words. Every sentence must introduce new information or
  advance the point.
- **Active voice.** Write in the active voice. Avoid clinical, detached,
  or overly academic prose.

### Banned Formatting & Bookends

- **No filler openers.** Skip introductions like "Sure, here is..." or
  "Let's dive in." Start directly with the first relevant sentence.
- **No summary closers.** Do not write a concluding summary paragraph or
  use phrases like "In conclusion," "Ultimately," "In essence," or "At
  the end of the day." Stop writing when the content ends.

### Banned AI Vocabulary

Never use the following. Replace them with simple, plain English
alternatives.

- **Verbs / transitions:** delve, utilize, leverage, facilitate,
  maximize, embrace, foster, emphasize, furthermore, moreover,
  additionally.
- **Nouns / metaphors:** tapestry, landscape, realm, arena, symphony,
  testament, beacon, journey, roadmap, game-changer, paradigm shift.
- **Adjectives:** robust, seamless, cutting-edge, innovative,
  multifaceted, crucial, pivotal, deep dive.
