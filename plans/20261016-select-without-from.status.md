# Queries without FROM, slice 6a of ADR 0012: status

Created 2026-10-16. Status: open.
Task: [20261016-select-without-from.task.md](20261016-select-without-from.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), Amendment 5, "Queries
without FROM (slice 6a)".

## Relevant files

- Frontend: `belay/sqlite/syntax_select.py`.
- Resolution: `packages/belay-sqlite/Belay/Sqlite/Resolution/Queries.lean`,
  `Resolution/Sources.lean`, `Resolution/Syntax.lean`.
- Queries: `Resolution/QueryForm.lean`, `QueryJoins.lean`, `QueryJoinLaws.lean`,
  `QueryEval.lean`.
- Conformance: `packages/verifier-conformance/VerifierConformance/Outputs.lean`.

## Progress

- 2026-10-16: task and status files, stacked on #141 (Amendment 5). Native facts checked on
  SQLite 3.51.0: `count(*) WHERE 0` is one row 0; `SELECT *` is `no tables specified`;
  `a` and `t.a` are `no such column`; `GROUP BY 1` is one row.

## Remaining

- Implementation, full checks, CI time, pull request A; then pull request B (claim
  corpus 21, `mustAgree`).
