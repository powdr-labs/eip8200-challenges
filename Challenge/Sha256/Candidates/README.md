# Candidates

Work-in-progress SHA-256 implementations whose `Correct` proof is **not
finished**, kept deliberately outside [`../Submissions/`](../Submissions/).

`Submissions/` is a trust boundary: `scripts/check-sha256-submissions.sh`
requires every directory under it to carry `correct : Correct bytecode` with a
clean transitive axiom footprint, and it is right to. A candidate that cannot
yet meet that bar does not belong there, and should not be able to sit there
looking as though it does.

This directory is for the interval before that: bytecode that is finished,
scored and reproducible, with a proof that is under way and honestly labelled.
Nothing here is imported by `Challenge.lean`, so CI does not build it and never
treats it as evidence of anything.

Each candidate directory is expected to state, in its own README and without
euphemism, which of its results a machine has checked and which have only been
written.

| candidate | gas vs reference | proof |
|---|---|---|
| [`Sha256Fast`](Sha256Fast/) | 7.25× (8.46× unrolled variant) | partial — block lemmas checked, iteration lemmas written but not yet elaborated |

*This directory is a proposal, not an established convention — including its
name, which overlaps with the repository's existing use of "candidate" for a
finished entry under `Submissions/`. `Drafts/`, `Incubating/`, or nothing at all
would all be fine; if the maintainers prefer one, it moves or goes.*
