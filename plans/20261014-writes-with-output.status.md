# Status: writes with output, slice 3a of ADR 0012

Created 2026-10-14. Status: IN PROGRESS.
Task: [task](20261014-writes-with-output.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Slices", item 3, as
narrowed by the owner to slice 3a.

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Resolved.lean`,
`Resolution/Writes.lean`, `Resolution/Values.lean`, `Resolution/Queries.lean`
(`resolveResultColumn`), `SqlExecution.lean`, `LiteralData.lean`,
`packages/verifier-conformance/VerifierConformance/Outputs.lean`,
`belay/sqlite/syntax_writes.py`, `belay/sqlite/syntax_queries.py`.

## Findings

- 2026-10-14: survey of the write model. Writes resolve to literal rows and
  `(position, value)` assignments and filters; `insertReady` and `updateReady`
  check `lossless` stored values, which `Contract.lean` requires through
  `SupportedSql`. No code applies an affinity conversion when it stores a value.
  Row-dependent writes would change these obligations, so the owner chose slice 3a
  (constant expressions and `RETURNING`) and an amendment of ADR 0012 for the rest.
- 2026-10-14: native checks of `RETURNING` on 3.51.0: names as `SELECT` result
  columns (`b` on `B` is `B`; `rowid` and `oid` are `rowid`); `count(*)` and a missing
  name are prepare errors; a NOT NULL failure returns no rows; an `UPDATE` that
  matches nothing returns the column names and no rows.

## Progress

- 2026-10-14: task and status files created.
- 2026-10-14: constant expressions in writes. `constantValue` (QueryExprs) resolves a
  `VALUES` item or `SET` value as a query expression with no column in scope and
  evaluates it; `assignedValue` restricts an expression that names a column
  (`mentionsColumn`). Native checks: aggregates in `VALUES` and `SET` give `misuse of
  aggregate function`. `ValueIssue.under` moved to `Values.lean` so that `Writes`
  can import `QueryExprs`. `OperandIssues.lean` proves that issues of
  `resolveOperand` name no catalog object, for the prepare-error rules of INSERT and
  UPDATE; `queryNumeric` became one match so that the proof can split it.
- 2026-10-14: `RETURNING`. `Syntax.Statement.returning` wraps an INSERT or UPDATE with
  its result columns, so a write without `RETURNING` keeps its JSON record exactly
  (the retained regression evidence compares it byte for byte; Lean's derived JSON
  decoder needs every constructor field, so an optional field did not work).
  `Resolved` writes carry `returning : List (Expr × String)`; `Returning.lean`
  resolves the columns last, as SQLite does (values and filter errors come first),
  with `*`, `SELECT` naming, aggregates as misuse and rowid names as a restriction.
  `Outputs.statementOutput` gives the rows over the inserted rows or the new values
  of the selected rows, and names with no rows on a constraint failure. The frontend
  maps `RETURNING` and query expressions in writes. The verdict passes; corpus-v5
  has 217 AGREE (210 before).
- 2026-10-14: the amendment for slice 3b is proposed in #111 (docs only, for the
  owner); it lists six open questions.
- 2026-10-14: evidence. `conformance/authored_writes.py` has 16 cases; all agree and
  have kernel proofs (`tests/conformance_query_coverage_test.py`).
  `conformance/write_mutants.py` has the 5 mutants of the task with their target
  cases; with the query and number mutants, each changes a verdict. `write_evidence.py`
  writes the cases as corpus version 9 for PR B.
- 2026-10-14: CI timing (forced rebuild, 8 cores): `tests` main 314 s, branch 330 s
  (+16 s, 5 %); suites alone: `model` 150 s to 160 s, `mutants` 104 s to 119 s.

## Remaining

- PR A; then PR B (judge: claim corpus-v9 and the newly agreeing cases).
