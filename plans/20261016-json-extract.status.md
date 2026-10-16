# JSON reading and json_extract, slice 6b of ADR 0012: status

Created 2026-10-16. Status: open.
Task: [20261016-json-extract.task.md](20261016-json-extract.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), Amendment 5, "JSON reading
and `json_extract` (slice 6b)".

## Relevant files

- Frontend: `belay/sqlite/syntax_expressions.py`, `belay/sqlite/syntax_queries.py`.
- Resolution: `packages/belay-sqlite/Belay/Sqlite/Resolution/QueryExprs.lean`,
  `Resolution/QueryForm.lean`.
- Evaluation: `QueryEval.lean`, `NumberConvert.lean`.
- Conformance: `packages/verifier-conformance/VerifierConformance/Outputs.lean`.

## Progress

- 2026-10-16: task and status files, stacked on #143 (slice 6a, PR B). Native facts
  checked on SQLite 3.51.0, one statement per line: whitespace and comments are
  removed; `é` is decoded and `\n` and `\"` stay escaped; JSON5 numbers are
  normalized (`0x1F` 31, `.5` 0.5, `Infinity` 9e999, `NaN` null); an integer beyond 64
  bits and `1E400` are REAL (`Inf`); `$[-1]` is a bad path and `$[#-1]` the last element;
  `json_extract` with one argument is NULL; INTEGER and REAL arguments are read as text.

- 2026-10-16: native facts on evaluation: short-circuits, `X AND 0` folding, `LIMIT` and
  deferred result columns under `ORDER BY` decide whether an error occurs; recorded in
  the task's key points.

## Remaining

- Implementation, full checks, CI time, pull request A; then pull request B (claim
  corpus 22, `mustAgree`).
