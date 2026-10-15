# Status: RIGHT and FULL joins (slice 4c)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-right-full-joins.task.md).
Specification: [ADR 0012, Amendment 3, "Rows (slice 4c)"](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/QueryEval.lean`,
`QueryJoinLaws.lean`, `Resolution/QueryForm.lean`, `Resolution/Sources.lean`,
`Resolution/JoinUsing.lean`, `Resolution/Restrictions.lean`,
`Resolution/RestrictionText.lean`, `conformance/restriction_examples.py`,
`docs/semantic-subset.md`.

## Progress

- 2026-10-15: Amendment 3 accepted (#124); task and status files created. Native 3.51.0
  checked for the rows of right and full joins with and without `ON`, after inner and
  left joins, before a left join, two full joins, empty left and right tables,
  aggregates over padded rows, and `ON clause references tables to its right`.
- 2026-10-15: the model: `Resolved.JoinKind` has `right` and `full`; the join evaluation
  moved to `QueryJoins.lean`, where `joinRows` takes the width of the left input and adds
  the rows of `unmatchedRight` for right and full joins, and `Query.source` folds the
  widths of the tables. Laws: the width of every joined row, a left or full join keeps
  every left row, and a right or full join keeps every right row. `right-or-full-join`
  leaves the registry; `using-with-right-join` refuses `USING` and `NATURAL` in a `FROM`
  with a right or full join until slice 4d. The left-join mutants of slice 4 follow the
  moved code. Lean examples in `Resolution/RightJoinExamples.lean`.

## Remaining

- Full checks, CI time, PR A; then PR B (claim corpus 15, `mustAgree`).
