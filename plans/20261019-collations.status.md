# Status: collations (ADR 0014, slice 3)

Created 2026-10-19. Status: open.
Task file: [task](20261019-collations.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D3.

## Relevant files

- Values: `packages/belay-sqlite/Belay/Sqlite/Comparison.lean`, `QueryEval.lean`,
  `LiteralData.lean`.
- Resolution: `Resolution/QueryForm.lean`, `Resolution/QueryExprs.lean`,
  `Resolution/Queries.lean`, `Resolution/JoinUsing.lean`, `Resolution/Keys.lean`,
  `Resolution/IndexTerms.lean`, `Resolution/Definitions.lean`.
- Frontend: `belay/sqlite/syntax_definitions.py`, `syntax_queries.py`.
- Harness: `packages/verifier-conformance/VerifierConformance/Native.lean`, `Json.lean`,
  `Predict.lean`, `conformance/native_metadata.py`, `conformance/predict_render.py`.
- Tests: `Resolution/CollationExamples.lean`, `conformance/authored_collations.py`,
  `collation_evidence.py`, `collation_mutants.py`.

## Progress

- 2026-10-19: native behaviour checked with 3.51.0: `RTRIM` removes trailing spaces before
  a binary comparison (`'a '` < `'a\t'`), so every collation is a total order;
  `NOCASE` folds ASCII only; ORDER BY, `=`, GROUP BY and `min`/`max` over a `NOCASE`
  column use it; `COLLATE BINARY` on the right operand overrides the left column's
  collation; an unknown name is `no such collation sequence: FOO`.

- 2026-10-19: outcomes 1 to 6 in one commit. `Collation` with `key`, `compare` (a
  `Std.TransCmp`, so the sort laws keep their proofs) and `sqlName`; the resolved forms
  store the collation of a comparison, a sort term, a grouping term and `min`/`max`;
  `Resolution/Collations.lean` decides them; catalog columns and index keys carry one;
  keys, grouping, sorting and the `WITHOUT ROWID` scan compare through it. Native checks
  that changed the task: an unknown name outside a column definition and an index term
  is the restriction `unknown-collation` (SQLite's planner decides whether it looks it
  up); the `USING` equality has the left-most left column's collation; an ON CONFLICT
  target without `COLLATE` matches any key, so the target code stays. A `GROUP BY` term
  may be a column under `COLLATE`. The harness gives `NativeIndex.collations` and the
  prediction's column collations only when not `BINARY`. Six mutant anchors follow the
  changed texts. Authored corpus `authored_collations` (27 cases, all AGREE locally,
  corpus 31) and `collation_mutants` (three).

- 2026-10-19: checks. Fixes after the first suite runs: the authored catalog has one more
  case that agrees (`index-collation`) and the core closure three more modules; the kernel
  did not reduce `Syntax.Expr.collatedColumn`, whose recursion went through a nested
  pattern, so a `GROUP BY` term now admits one `COLLATE` (a second one stays
  `group-by-term`), with a kernel-checked example. Two files split to stay under 200
  lines (`Resolution/ResolvedExprForm.lean`, `Resolution/QueryTerms.lean`).
  `just test-full`, `just test-nix` and `just test-scheduled` pass. Verdict: 92 upstream
  cases newly agree (v3 +1, v4 +1, v5 +90), none leaves AGREE; corpus 31 (27 cases)
  agrees in full and has kernel proofs.

- 2026-10-19: CI time (local, forced rebuilds), slice 2 → slice 3: harness 22 → 21 s,
  model 352 → 364 s, frozen 142 → 140 s, mutants 466 → 519 s (three new mutants). PR B:
  corpus 31 recorded natively (27 cases) and claimed in full; the 92 upstream cases join
  `mustAgree`; new judge lock.

## Remaining

- Pull requests A and B.
