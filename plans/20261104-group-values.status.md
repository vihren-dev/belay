# The values of a group: task status

Date: 2026-11-04. Status: OPEN.
Audience: the implementation team.
Task: [The values of a group](20261104-group-values.task.md).
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md).
Source baseline: the end of slice 1 ([status](20261104-conditional-creation.status.md)).

Relevant files: `packages/belay-sqlite-model/Belay/Sqlite/Model/QueryResults.lean`,
`QueryEval.lean`, `Resolution/QueryForm.lean`, `Resolution/QueryBodyTraced.lean`,
`Resolution/QueryAggregates.lean`, `DuplicateKeyQuery.lean`, `PossibleResults.lean`,
`docs/semantic-subset.md`; new: `GroupRow.lean`, `Resolution/GroupAssociation.lean`,
`conformance/authored_group_values.py`, `tests/surface/ClaimsGroupValues.lean`.

Tests of the slice: `tests/conformance_group_values_test.py` (all 39 cases agree),
`tests/surface_group_values_test.py`, `tests/lean_packages_test.py`.

## Progress

- 2026-11-04: task specified.
- 2026-11-04: the row of a group and the association (D5). The resolver records the deciding
  call (`Query.deciding`) and the result columns that read the first row
  (`Query.firstRowColumns`); `Query.groupRow` gives the row of a group. Authored corpus
  `group-values-*` (35 cases) and the surface example. Local checks: dev-build, dev-verdict (no
  claimed verdict changes), the slice's tests. `INSERT ... SELECT` from a grouped source is
  outside the subject's scope, so the corpus has no such case. The probes found one more SQLite
  rule (an associated column in `ORDER BY` with two or more grouping terms); the ADR records it
  as a dated note in D5, and the corpus has no such case.
- 2026-11-04: review fixes (`refactor:`): the deciding call compares repeated calls as written
  (`Syntax.Expr.sameIn`), so `max(n)` and `max(+n)` are two calls, with the corpus cases
  `group-values-repeated-with-plus` and `group-values-repeated-other-spelling`; proof sketches
  of the deciding-call lemmas; the documentation of the association and of the `ORDER BY`
  exception.
- 2026-11-04: review fix (`refactor:`): small integer literals compare by value in
  `Syntax.Expr.sameIn` (`smallIntegerLiteral`), as SQLite's parser stores them, with the corpus
  cases `group-values-repeated-integer-spelling` and `group-values-repeated-real-spelling`.
