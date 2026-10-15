# Status: USING and NATURAL joins (slice 4b)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-using-natural.task.md).
Specification: [ADR 0012, Amendment 2, "Owner decisions", item 1](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Scope.lean`,
`Resolution/Sources.lean`, `Resolution/Queries.lean`, `Resolution/QueryExprs.lean`,
`Resolution/Restrictions.lean`, `Resolution/RestrictionText.lean`,
`Resolution/JoinExamples.lean`, `QueryJoinLaws.lean`, `conformance/authored_joins.py`,
`conformance/restriction_examples.py`, `docs/semantic-subset.md`.

## Progress

- 2026-10-15: task and status files created. Native 3.51.0 checked for the task's
  rules: the merged columns in `*`, `x.*` and unqualified names; the left-most left
  column (`FROM t, u NATURAL JOIN v`); the comparison affinity (`'02'` matches `2`);
  `NATURAL` without a common column; a repeated `USING` name; both prepare errors and
  their order after `no such table`.
- 2026-10-15: the model: `Source.merged` hides merged columns from `*`
  (`Scope.visible`) and unqualified names; `Resolution/JoinUsing.lean` generates the
  condition as qualified syntax, so a written `ON` and `USING` resolve the same, with
  three proofs (`mergeJoin_written`, `mergeJoin_using`, `mergeJoin_natural`);
  `resolveTables` resolves every table before the join forms; the errors
  `joinUsingColumn` and `naturalJoinCondition`; `join-using` and `natural-join` leave the
  registry. Lean examples in `Resolution/UsingExamples.lean`. The INTEGER and TEXT case
  moved from the native cases to a Lean example: the comparison is the restriction
  `mixed-affinity-comparison`, as for a written `ON`, so no native case can agree.
- 2026-10-15: review of the model commit (1 must, 1 should, fixed): a proof sketch for
  `usingNames_checked`; explicit statement cases in `UsingExamples.queryOver`.

## Remaining

- Full checks, CI time, PR A; then PR B (claim corpus 14, `mustAgree`).
