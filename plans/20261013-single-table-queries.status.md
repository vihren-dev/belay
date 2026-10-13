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
- 2026-10-13: value comparison (`Comparison.lean`), the resolved query form with
  its evaluation, laws and examples, `Resolved.Statement.query` through the model
  and its outputs, and resolution of `Syntax.Statement.select`; each reviewed.
- 2026-10-13: frontend `belay/sqlite/syntax_queries.py`; function calls keep the
  name as written and Lean folds it. Bringing SELECT into scope exposed three corpus
  disagreements: `sqlite_master` queries (now a restriction), standard type names
  that SQLite reports in capitals (`reportedType`; this bug was already on main), and
  a result column alias in `WHERE` (altercol-15.0, now a restriction). The verdict
  passes; corpus-v5 has 194 AGREE and no DISAGREE.

## Remaining

- Authored query coverage cases, query mutants, model cases with queries, CI
  timing, PR A; then PR B (judge: claim a query corpus, mustAgree cases).
