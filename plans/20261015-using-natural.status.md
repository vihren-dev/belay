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

## Remaining

- Everything in the task's "Outcome".
