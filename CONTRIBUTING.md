# Contributing to leanp2p

Thanks for your interest. leanp2p is a Lean 4 implementation of
libp2p. Its first target is the Ethereum consensus layer, and its
protocol cores are machine-checked. Contributions are welcome.

## Status

The project is in bootstrap. The `main` branch carries the documents,
and the packages land in the order of [`docs/PLAN.md`](docs/PLAN.md).
Until PLAN unit W0 lands, the branch has no build. The `spike` branch
holds the reference implementation.

## Quick start

```bash
# 1. Install elan (one time). https://elan.lean-lang.org/
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# 2. Install the native dependencies.
# Linux (Debian/Ubuntu):
sudo apt-get install libssl-dev pkg-config
# macOS:
brew install openssl@3 pkg-config
```

Elan picks up the pinned toolchain from `lean-toolchain`. Once W0
lands, `lake build` builds every package, and `lake test` runs the
vector suites. The suites must also pass under `+RTS -N1`.

## Where to start

- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) is binding on
  substance: contracts, dependency rules, priorities.
- [`docs/PLAN.md`](docs/PLAN.md) is binding on order. Claim a unit
  there before you start it.
- [`docs/PRINCIPLES.md`](docs/PRINCIPLES.md) explains each engineering
  rule and the incidents behind it.
- Every package carries its own `docs/ARCHITECTURE.md` and
  `docs/PLAN.md`. They refine the root documents.

## Code style and discipline

[`CLAUDE.md`](CLAUDE.md) at the repository root documents the
conventions in detail. The short version:

- **Literate by default.** Comments teach the spec and the Lean idioms
  as the file unfolds. A libp2p reader should not need advanced Lean,
  and a Lean reader should not need to know libp2p.
- **Strict checking.** `set_option autoImplicit false` in every file.
  No committed `sorry`, `#eval`, `#check`, or `#print`.
- **One home per fact.** A frame layout or a protocol constant lives in
  one module, and every other module imports it.
- **Bounded inputs.** Every length-prefixed read has a cap that applies
  before allocation (ARCHITECTURE.md §5).
- **Spec is the source of truth.** The libp2p and multiformats specs
  and the captured vectors decide behavior. When another implementation
  disagrees with the spec, the spec wins, and we record the
  discrepancy.

Read the *Principles* and *Conventions* sections of `CLAUDE.md` before
you send a non-trivial pull request.

## Pull requests

- Keep the diff focused: one pull request per logical change.
- Run `lake build` and `lake test` before you push.
- A new codec comes with its round-trip theorem or property test. New
  proof code comes with an `example` block that the typechecker checks.
- A new framing layer comes with its length cap and a test that sends
  an over-long length.
- List every axiom, `sorry`, `partial def`, `native_decide`, `unsafe`
  block, or `@[extern]` declaration that the change adds or removes.
  The pull request template has a section for it.
- Do not list an AI agent as a co-author, and do not put an AI session
  tag in a commit message. The `AI co-author guard` workflow rejects
  both.

The repository uses the standard GitHub review flow. One approval from
a maintainer is the gate.

## Reporting issues

- **Bugs in wire behavior**: open a GitHub issue with a minimal
  reproducer (a Lean snippet, a byte sequence, or a transcript) and the
  expected and actual output. Name the spec section or the vector that
  the code breaks.
- **Interop failures**: name the peer implementation and its version,
  the transport stack, and the side that dialed.
- **Security vulnerabilities**: do *not* file a public issue.
  [`SECURITY.md`](SECURITY.md) describes the private disclosure
  process.

## Licensing

The project is licensed under LGPL-3.0-or-later (see
[`LICENSE`](LICENSE)). By contributing, you agree that your
contributions are licensed under the same terms.

Every pull request states that agreement in its own description. The
pull request template ends with the acceptance line, already ticked:

```
- [x] I have read and accepted LICENSE (LGPL version 3), NOTICE and CLA in the root of this project.
```

Leave that line in place. The `License acceptance guard` workflow reads
the description and fails if the line is unticked or deleted. Restore it
and the check re-runs on the edit; no new commit is needed.
