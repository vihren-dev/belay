# Status: USING and NATURAL with RIGHT and FULL joins (slice 4d)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-using-with-right-joins.task.md).
Specification: [ADR 0012, Amendment 3, "Names with USING and NATURAL (slice 4d)"](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Scope.lean`,
`Resolution/QueryExprs.lean`, `Resolution/JoinUsing.lean`, `Resolution/Sources.lean`,
`Resolution/Returning.lean`, `Resolution/Queries.lean`,
`Resolution/RestrictionText.lean`, `conformance/restriction_examples.py`,
`docs/semantic-subset.md`.

## Progress

- 2026-10-15: task and status files created. Native 3.51.0 checked for the rule of
  unqualified merged names over chains (right then full, full then right, full then
  inner, left then full), the REAL right column, the coalesce without affinity in
  `WHERE`, `GROUP BY` and `ORDER BY`, `*` of right and full joins, the coalesced left
  side of a later `USING`, and `ambiguous reference to a in USING()`.

## Remaining

- Everything in the task's "Outcome".
