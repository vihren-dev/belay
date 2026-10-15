# Status: key values (slice 5a)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-key-values.task.md).
Specification: [ADR 0012, Amendment 4, "Key values (slice 5a)"](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/LiteralData.lean`, `RowUpdate.lean`,
`Comparison.lean`, `LiteralPreservation.lean`, `WritePreservation.lean`,
`Resolution/KeyDomain.lean`, `Resolution/Writes.lean`, `Resolution/Updates.lean`,
`Resolution/Restrictions.lean`, `Resolution/RestrictionText.lean`,
`conformance/obligation_mutants.py`, `conformance/authored_obligations.py`,
`conformance/restriction_examples.py`, `docs/semantic-subset.md`.

## Progress

- 2026-10-15: Amendment 4 accepted (#131, with owner decision 4: two key slices); task
  and status files created. Native 3.51.0 checked for key equality of TEXT, REAL,
  NUMERIC and untyped keys, composite keys with NULL, and NOCASE keys.

## Remaining

- Everything in the task's "Outcome".
