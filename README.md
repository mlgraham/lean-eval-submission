# lean-eval submission — finite_graph_ramsey_theorem (original proof)

Submission workspace for the [lean-eval](https://github.com/leanprover/lean-eval) benchmark
problem `finite_graph_ramsey_theorem` (the finite Ramsey theorem for graphs).

## Provenance

**This is an original proof**, written by Claude Fable 5 (Claude Code) under human direction,
using only the problem's `Challenge.lean`, the workspace's pinned Mathlib (source and grep),
and the Lean compiler's feedback. No published lean-eval solution to any problem was consulted
(this branch's submitter also maintains a separately-labeled packaging entry; the two are kept
in disjoint buckets and disjoint branches deliberately).

Proof shape: a Finset-strengthened statement — for all `r s`, some `n` bounds a finset `A` in
*any* graph on *any* vertex type such that `A` contains an `r`-clique of `G` or an `s`-clique
of `Gᶜ` — proved by double induction on `r` and `s` with the classic pivot-vertex pigeonhole
(`R(r+1,s+1) ≤ R(r,s+1) + R(r+1,s) + 1`), keeping the whole argument in one vertex type so no
induced-subgraph transfer is needed; the benchmark statement follows by specializing to
`Fin n` and `A = univ`. Mathlib (at the workspace's pin) has no Ramsey theorem to cite; the
proof builds on `SimpleGraph.IsNClique.insert`, `card_filter_add_card_filter_not`, and the
clique API.

Solver-owned files: `Submission.lean`, `Submission/Helpers.lean`. Everything else is the
unmodified generated workspace from `leanprover/lean-eval`.
