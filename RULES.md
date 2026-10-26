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
label. The dependency tree of the issues is the build order: an issue
opens for claims only when every issue it depends on is closed, and
closed means merged.

## Claiming an issue

1. Pick an issue whose dependencies are all closed, merged included.
2. Comment `claim` on the issue. An organiser assigns it to you. You
   hold one issue at a time.
3. Open a pull request within 8 hours of the assignment. The clock is
   UTC, drafts count, and the pull request links the issue with
   `Closes #N`.
4. Miss the window, lose the claim. The issue is unassigned, and
   anyone can claim it again.
5. Organisers review within 12 hours. When the pull request merges,
   the issue closes, and the issues that depend on it open for
   claims.
6. Repeat, all week.

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
  opened before code close and merged.
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
