# Status: numbers in queries, slice 2 of ADR 0012

Created 2026-10-13. Status: IN PROGRESS.
Task: [task](20261013-query-numbers.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Slices", item 2.

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Comparison.lean`,
`QueryEval.lean`, `QueryLaws.lean`, `Resolution/QueryForm.lean`,
`Resolution/QueryExprs.lean`, `Resolution/Queries.lean`,
`Resolution/Values.lean`, `Resolution/Syntax.lean`, `SqlExecution.lean`,
`packages/verifier-conformance/VerifierConformance/Outputs.lean`,
`belay/sqlite/syntax_queries.py`, `conformance/authored_queries.py`,
`conformance/query_mutants.py`. SQLite source: the 3.51.0 amalgamation from
`sqlite-autoconf-3510000.tar.gz` (line numbers in the task file).

## Findings

- 2026-10-13: the pinned Lean evaluates `Float` in the kernel (`Float.ofModel`),
  with correct IEEE results for addition, division, overflow to infinity and
  conversion of `2^53 + 1`. No own floating-point model is needed.
- 2026-10-13: `sqlite3AtoF` and `sqlite3FpDecode` use Dekker double-double steps
  and are not correctly rounded; they need exact ports. `SUM` can fail with
  `integer overflow` when the statement runs; `AVG` cannot.

## Progress

- 2026-10-13: task and status files created after slice 1 merged (#107, #108).
- 2026-10-13: `NumberText.lean` and `NumberConvert.lean` port `sqlite3AtoF` (with
  `dekkerMul2`), `sqlite3Atoi64` and `sqlite3RealToI64`. They agree with native
  `CAST(text AS REAL)` and `CAST(text AS INTEGER)` on 52 inputs, among them five
  where SQLite differs from correct rounding (for example `2.6018159083016613186e-270`);
  `NumberExamples.lean` keeps a set of them. One conversion takes about 2 s in the
  kernel; one `Float` operation about 5 ms.

## Remaining

- All outcome items of the task.
