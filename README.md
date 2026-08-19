# lean-eval submission — substInv_X_sub_X_sq_eq_catalan (packaged public accepted source)

Submission workspace for the [lean-eval](https://github.com/leanprover/lean-eval) benchmark
problem `substInv_X_sub_X_sq_eq_catalan` ("Catalan generating function via compositional
inversion").

## Provenance — read this first

**The proof in `Submission.lean` is not our work.** It was written by the
`savarin-6-hour-gpt-5.6-speedrun` entry (author: [savarin](https://github.com/savarin)),
published under the Apache-2.0 license in
[savarin/lean-eval-speedrun](https://github.com/savarin/lean-eval-speedrun) at commit
`ab459a1ea7a89ec6db93da77d522ea384a45d0aa`, and accepted by the lean-eval comparator on
2026-08-17 (their entry's public results record).

This repository repackages that published solution, unmodified, into a fresh comparator
workspace generated from the current `leanprover/lean-eval` benchmark, and verifies it
builds against the current trusted `Challenge.lean`. lean-eval explicitly permits copying
published solutions (see the submission form's "Publishing exact solutions" section);
the leaderboard entry name discloses the method.

The original `LICENSE` (Apache-2.0) from the source repository is included at the root,
as required by that license.

## Layout

- `substInv_X_sub_X_sq_eq_catalan/` — the comparator workspace: trusted files
  (`Challenge.lean`, `Solution.lean`, `WorkspaceTest.lean`, `lakefile.toml`, `config.json`)
  are unmodified from `leanprover/lean-eval`'s generated workspace; solver-owned files
  (`Submission.lean`, `Submission/Helpers.lean`) carry the packaged published proof.
