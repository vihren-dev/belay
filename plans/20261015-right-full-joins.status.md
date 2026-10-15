# Status: RIGHT and FULL joins (slice 4c)

Created 2026-10-15. Status: DONE.
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
- 2026-10-15: review of the model commit (1 must, fixed): explicit join kinds in
  `joinFormIssue`.
- 2026-10-15: 20 authored cases (`conformance/authored_right.py`, all AGREE), four
  mutants (`conformance/right_mutants.py`, in the write and join measurement), and the
  corpus 15 writer.
- 2026-10-15: CI time (local, `--check` rebuilds, main vs branch): mutants 159/168 s,
  model 202/213 s, frozen 139/138 s. Pull request A merged as #125.
- 2026-10-15: pull request B: corpus 15 (20 cases) is claimed. No case of the claimed
  corpora newly agrees: none uses a right or full join. New judge lock. Slice 4c is
  DONE; slice 4d (USING and NATURAL with right and full joins) follows.
