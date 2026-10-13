# Status: single-table queries, slice 1 of ADR 0012

Created 2026-10-13. Status: IN PROGRESS.
Task: [task](20261013-single-table-queries.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Syntax.lean`,
`Resolution/Resolved.lean`, `Resolution/Resolve.lean`, `Resolution/Writes.lean`,
`Execution.lean`, `SqlExecution.lean`, `SqlProofs.lean`, `Laws.lean`,
`Preservation.lean`, `packages/verifier-conformance/VerifierConformance/Outputs.lean`,
`belay/sqlite/syntax.py`, `belay/sqlite/syntax_expressions.py`.

## Findings

- Survey, 2026-10-13, on `main` `b725d252`: 12 match sites over
  `Resolved.Statement` and 4 over `Syntax.Statement`; expression resolution is
  in `Values.literalValue`, `Writes.assignedValue` and `Writes.resolveFilter`;
  the frontend maps `expr` productions in `syntax_expressions.expression` and
  refuses SELECT in `syntax.statement`.

## Progress

- 2026-10-13: ADR 0012 accepted by the owner and merged (#106); task and status
  files created.

## Remaining

- All outcome items of the task.
