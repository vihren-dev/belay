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
- 2026-10-13: `RealText.lean` ports `%!.15g` over `sqlite3FpDecode` (REAL to text).
  It agrees with native `CAST(real AS TEXT)` on 5033 doubles (edge cases, random
  bit patterns and random magnitudes).
- 2026-10-13: `Arithmetic.lean` ports `OP_Add` to `OP_Remainder` (with the numeric
  type of TEXT and BLOB operands) and `sqlite3VdbeMemCast`. It agrees with native
  SQLite on 6696 checks: 36 values (NULL, integers at the limits, REALs with
  infinities and signed zero, numeric and other TEXT, BLOBs) under each operator,
  unary minus as `0 - x`, and each `CAST` affinity.
- 2026-10-13: syntax, resolution and frontend for numbers in queries.
  `Syntax.Expr` gains `arithmetic`, `cast` and `callPair` (a call with two or more
  arguments as a chain, so that the frontend need not fold the name);
  `Resolved.Expr` gains `arithmetic`, `cast` and `coalesce`. REAL literals in
  queries take `sqlite3AtoF` values; `-expr` is `0 - expr`, `+expr` drops the
  affinity; `COALESCE` with one argument and `COUNT` with two give
  `wrongArgumentCount`; the hex error text keeps the minus sign. The affinity rules
  moved to `Resolution/QueryAffinity.lean`; a no-affinity operand that may be TEXT
  (a `COALESCE` with a column) is restricted against a numeric operand. The verdict
  passes; corpus-v5 has 202 AGREE (194 before).
- 2026-10-13: `SUM` and `AVG`. `Summation.lean` ports `sumStep`, `sumFinalize` and
  `avgFinalize` (Kahan-Babuska-Neumaier, the overflow flag, numeric affinity of TEXT
  inputs); it agrees with native SQLite on 406 random sequences, 12 of them with the
  overflow error. A query's step fails with `ExecutionError.integerOverflow` when
  `Query.fails` holds; its output is the column names and no rows without GROUP BY,
  and none with GROUP BY (SQLite may return other groups first). `SUM` in a grouped
  query with LIMIT or OFFSET is a restriction. The verdict passes; corpus-v5 has 210
  AGREE.
- 2026-10-13: evidence. `conformance/authored_numbers.py` has 31 coverage cases;
  all agree and have kernel proofs (`tests/conformance_query_coverage_test.py`, now
  over both case sets). `conformance/number_mutants.py` has the 13 mutants of the
  task; with the 16 query mutants, each changes a verdict
  (`tests/conformance_query_mutants_test.py`). `conformance/authored_evidence.py`
  is the shared corpus writer; `number_evidence.py` writes corpus version 8 for
  PR B.
- 2026-10-13: CI timing (forced rebuild, 8 cores): `tests` main 289 s, branch 335 s
  (+46 s, 16 %); suites alone: `model` 129 s to 149 s, `mutants` 66 s to 139 s. A
  mutant copy spends about 6 s in its build and 6 s elaborating the case terms;
  classifying from JSON cuts the second to 0.9 s but raises the build to 17 s
  (codec modules), so the term classifier stays.

## Remaining

- PR A; then PR B (judge: claim corpus-v8 and the newly agreeing cases).
