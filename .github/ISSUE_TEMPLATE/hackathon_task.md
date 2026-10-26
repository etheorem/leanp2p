---
name: Hackathon task
about: one work unit of docs/PLAN.md, for the Machine-Checked Devcon Week (label HACKATHON)
labels: HACKATHON
---

<!-- The organisers open these issues from docs/PLAN.md. The shape is
     fixed so the tracking issue and the dependency links stay
     uniform. -->

## Task

**Unit `W?.?` of [`docs/PLAN.md`](https://github.com/etheorem/leanp2p/blob/hackathon26/docs/PLAN.md).**

<deliverable: the one-line what, and the why in one sentence>

## Where the spec lives

- The unit row: root [`docs/PLAN.md`](https://github.com/etheorem/leanp2p/blob/hackathon26/docs/PLAN.md) (deliverable, dependencies, priority).
- The frozen interfaces: root [`docs/ARCHITECTURE.md`](https://github.com/etheorem/leanp2p/blob/hackathon26/docs/ARCHITECTURE.md), §3 (the mechanisms) and <§4.x> (this package).
- The package's own docs: `<packages/<group>/<pkg>/docs/ARCHITECTURE.md>` and its `PLAN.md` — read them first; they refine the root docs and never contradict them.
- The reference: the `spike` branch, `<modules>` (ARCHITECTURE §7). Read it before you implement. Port its tests, keep the wire bytes; the code shape follows §3, not the spike's internals (§7 preamble, §9).

## Your freedom, and its cost

The docs govern, and they are yours to change. Where a better design exists, change it — and change the documents in the same pull request. A contract change starts at the root `docs/ARCHITECTURE.md`; the package docs follow it in the same change. Code that disagrees with the docs, or package docs that disagree with the root, does not merge.

## Definition of done

- The public surface follows ARCHITECTURE §4; the owned contracts hold.
- <the proofs and tests this unit owns — scoring multiplies code quality by proof coverage>
- The carried vector and property tests pass through the `Tests` suite.
- `lake build`, `lake test`, and `lake test -- +RTS -N1 -RTS` are green; `scripts/lint-imports.sh` is green.
- No `sorry`, no build warnings (CLAUDE.md, "Strict checking").
- First submodule under your leaf? Widen the lib's `globs` in `lakefile.toml` in the same commit.

## Depends on

- #N (`W?.?`) — blocking. An issue opens for claims only when every dependency is closed, and closed means merged ([`RULES.md`](https://github.com/etheorem/leanp2p/blob/hackathon26/RULES.md)).

## Ground rules

- Comment `claim` to take the issue; an organiser assigns it. One issue at a time.
- A pull request within 8 hours of the assignment; drafts count. Link the issue (`Closes #N`). Miss the window, lose the claim.
- Target the `hackathon26` branch.
- The license-acceptance line of the PR description stays ticked; commits carry no AI co-author trailers. Two guards fail the PR otherwise.
- Prose register everywhere: CLAUDE.md, "Writing Style".
- A contract question the docs do not settle: ask on this issue before you code past it.
