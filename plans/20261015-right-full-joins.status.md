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

## Remaining

- Everything in the task's "Outcome".
