# leanp2p: Machine-Checked Devcon Week rules

The week runs 2 to 7 November 2026. It is an online hackathon run by
Invisible Garden during Devcon week; the
[event page](https://invisible.garden/machine-checked-devcon) carries
the announcement, the application form, and the prizes. This file is
the canonical copy of the work rules for this repository. The
community rules of Invisible Garden apply all week.

## The work

You implement pieces of Ethereum's networking layer in Lean 4 and
prove properties of what you build. Every proof is checked by Lean's
kernel, and implementation and proofs live together in one codebase.
The tasks are the issues of this repository that carry the HACKATHON
label. The dependency tree of the issues is the merge order. Every
issue is claimable from the start of the week, because the interface
of every unit is frozen in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
§4 ahead of the work. You may build ahead of your dependencies against
mocks of their frozen interfaces; the section after the claiming loop
says how.

## Claiming an issue

1. Pick any issue. When every dependency of the issue is merged, you
   build on the real code. When a dependency is still open, you build
   against a mock of its frozen interface.
2. Comment `claim` on the issue. An organiser assigns it to you. You
   hold one issue at a time.
3. Open a pull request within 8 hours of the assignment. The clock is
   UTC, drafts count, and the pull request links the issue with
   `Closes #N`.
4. Miss the window, lose the claim. The issue is unassigned, and
   anyone can claim it again.
5. Organisers review within 12 hours. When the pull request merges,
   the issue closes, and the owners of the dependent issues integrate
   the real code.
6. Repeat, all week.

## Working ahead of the tree

The interfaces of every unit are frozen in
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §3 and §4, so the tree
does not serialize the work. Claim any issue on day one. When a
dependency of your issue is not merged yet, build against a mock of
its frozen interface.

- The mock lives in a `Mock` namespace inside your package. It
  declares the surface of the dependency, the types and the constants,
  with `opaque` declarations, and it imports nothing from the real
  package.
- Where your proofs need a theorem of the dependency, state the
  theorem as an axiom of the mock. `#print axioms` in the pull request
  body lists every mock axiom you assumed. No `sorry` anywhere, and CI
  stays green.
- A pull request with mocks can open and go through review. It merges
  only when every dependency of its issue has merged. The merge is the
  integration point.
- When your last dependency merges, you drop the mocks and integrate
  within 12 hours. After the window, the pull request waits at the end
  of the review queue until it is green without mocks.

The frozen interfaces stay frozen for the week. A change that breaks
a frozen interface needs the approval of an organiser on the issue
first, and you post a comment on every issue that depends on yours.
The owners of the dependent issues rebase after your change lands.

## Deadlines

- Code closes 7 November 2026, 23:59 UTC. Every pull request you want
  judged must be open by then, with CI green. Merges can land later.
- Video by 15 November 2026, 23:59 UTC. Up to 10 minutes, you
  explaining your contributions; the link goes in the event channel.
  Unlisted is fine. Without a video, the work is not judged.
- Judging by 20 November; results by 30 November.

## Scoring

Submissions are scored on two axes, code quality and how much of the
work carries machine-checked proofs, and the final score multiplies
the two. Well engineered code earns its value together with proofs.
The proofs the repository counts are the ones of ARCHITECTURE §6: the
theorems over the pure cores, the `LawfulCodec` laws, the fuzz pinning
of the production paths, and the transcript tests on the protocol
cores.

## Prize eligibility

Prizes recognise meaningful contributions. The judges assess your
whole body of merged work from the week, and they have the final say
on what counts. The baseline:

- Your work closes at least one claimed issue, with the pull request
  opened before code close and merged. A pull request that is open at
  code close with CI green, and is blocked only by dependencies that
  did not merge in time, also counts. State the blocker in your video.
- The contribution is real implementation work or real proof work.
  Mechanical changes, typo fixes, formatting, dependency bumps, and
  trivial refactors do not count by themselves.
- You can explain and defend your work in the video, your reasoning
  and your proofs included. A contribution you cannot defend in the
  video does not count for prizes.
- All counted work falls inside the event window, 2 to 7 November.

If a participant's overall contributions stay at a basic level, the
judges may rule them out of prize consideration. The work stays
public either way, and every merged pull request is yours to show.
With fewer than 7 active participants, the prize pool can be reduced.

## How to work in this repository

The repository's own rules bind every pull request: [`CLAUDE.md`](CLAUDE.md)
for the conventions and the writing style, [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
for the contracts, [`docs/PLAN.md`](docs/PLAN.md) for the order, and
[`CONTRIBUTING.md`](CONTRIBUTING.md) for the pull request workflow and
the toolchain setup. Pull requests target the `hackathon26` branch.
The license-acceptance line of the pull request description stays
ticked, and commits carry no AI co-author trailers; two guards fail
the pull request otherwise.

Questions go to the event channel on the
[Invisible Garden Discord](https://discord.gg/SxvYP4vvg) all week.
Organisers and mentors answer there, and acceptances are announced
there.
