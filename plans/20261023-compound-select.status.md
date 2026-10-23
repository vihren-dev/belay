# Status: compound SELECT (ADR 0019, slice 3)

Created 2026-10-23. Status: OPEN (the task file is written; the implementation has not started).
Task file: [task](20261023-compound-select.task.md).
Specification: [ADR 0019](../docs/adr-0019-guide-sql.md), D3 and D7.

## Progress

- 2026-10-23: the task file, from the code after ADR 0017's S3, native probes with the dev
  shell's `sqlite3` 3.51.0 (one statement for each line), SQLite's `select.c`, `resolve.c`,
  `expr.c` and `parse.y` of 3.51.0 (`sqlite-conformance-upstream-3.51.0` in the Nix store), and
  `experiments/model-gaps/next_groups.py` over the Nix verdict after slice 1.
- 2026-10-23: review round 1 (three musts) fixed with native probes: the 32-bit rule for an
  `ORDER BY` column number, no collation for a scalar subquery, and the point where SQLite reads
  `LIMIT` and `OFFSET` for each operator (task file, outcomes 7, 9 and 10).

## Owner decisions (open)

1. **D3 and the columns of a compound.** D3 says that each column compares under the collation of
   a compound column (the left-most `SELECT` whose column has one). This is true for the
   duplicate rule and for an `ORDER BY` term without `COLLATE`. Two rules of SQLite differ, and an
   implementer acts on them:
   - `x IN (q)` over a compound reads the affinity and the collation of the right-most term's
     column, and a scalar `(q)` only its affinity (a subquery has no collation), not the compound
     collation (task file, outcome 9; `'A' IN (SELECT n FROM t UNION SELECT m FROM u WHERE 0)` is
     0 for a `NOCASE` column `n` with `'a'` and a `BINARY` column `m`).
   - When an operator is not `UNION ALL` and an `ORDER BY` term has `COLLATE`, a term without
     `COLLATE` sorts under the collation of the left-most term's expression, not the compound
     collation (outcome 7, `convertCompoundSelectToSubquery`).
   Recommendation: amend D3 with both rules, as the repository follows native SQLite. The task
   file already states them.
2. **A compound as a statement of a trigger body.** D3 says that a compound may be a statement.
   The task file keeps a compound `SELECT` statement in a trigger body refused by the frontend
   (`Translation/Triggers.lean`); a compound subquery inside a trigger body's statement is in
   scope. A lexical count over the out-of-scope cases after slice 1 finds at most 11 cases of v5
   and 11 of v4 with a compound in a trigger. Recommendation: keep it out of slice 3, and say so in
   the amendment of D3; add it when a measurement or a guide example needs it.

## Notes for later slices

- **Slice 5 (D4)** makes a compound the source of `INSERT`. `valueRows`
  (`Translation/Writes.lean`) keeps its refusal until then.
- **Slice 4 (D5)** reads a compound as a derived table, a view or a common table expression.
  Such a source column has other rules (`sqlite3SubqueryColumnTypes`): the collation of the
  left-most term's expression only, and an affinity from the types of the terms. Native, over
  `t(n TEXT COLLATE NOCASE)` with `'B'` and `'a'`: `SELECT 'b' AS x UNION ALL SELECT n FROM t ORDER
  BY x` gives `'a'`, `'b'`, `'B'`, and `SELECT x FROM (SELECT 'b' AS x UNION ALL SELECT n FROM t)
  ORDER BY x` gives `'B'`, `'a'`, `'b'` (`BINARY`).

## Measurement

Over the Nix verdict after slice 1 (2026-10-23): 274 of 1,881 out-of-scope cases of v5 and 36 of
624 of v4 have a compound mark; with compound `SELECT`, 228 more cases of v5 and 18 of v4 have no
mark left. These are upper bounds. Log: `build/agent-logs/adr19s3-next-groups.json` (local).

## Files

- Model: `Resolution/Syntax.lean`, `Resolution/SyntaxExpr.lean`, `Codec/SyntaxJson.lean`,
  `Resolution/QueryForm.lean`, `Resolution/Queries.lean`, `Resolution/QueryTerms.lean`,
  `Resolution/Collations.lean`, `Resolution/SubqueryShapes.lean`,
  `Resolution/SubqueryResolution.lean`, `Resolution/SelectResolution.lean`, `QueryResults.lean`,
  `QueryRun.lean`, `QueryWindow.lean`, `Subqueries.lean`, `PossibleResults.lean`,
  `StatementOutput.lean`, `StatementStep.lean`, `StatementClock.lean`, `SqlLaws.lean`.
- Frontend: `Translation/Select.lean`, `Translation/Subqueries.lean`, `Translation/Statements.lean`.
- Conformance: `conformance/authored_queries.py` (`QueryCase`), `authored_evidence.py`,
  `parameter_evidence.py` (the model of a writer), `parameter_mutants.py`, `resolve_mutants.py`,
  `native_ordering.py` and `query_window.py` (the limits of the recorder).

## Tests for each commit

The tests that touch the commit, then `just review`: the frontend tests
(`tests/syntax_queries_test.py` and the new compound tests), `tests/conformance_model_test.py`,
`tests/conformance_pipeline_test.py`, and for the corpus `tests/conformance_query_coverage_test.py`
and `tests/conformance_corpus_writers_test.py`; `just dev-build` and `just dev-verdict` for each
edit of `packages/`.

## Remaining

- The implementation, the authored corpus, the mutants, the surface fixture, `just test-full` and
  `just verdict` at the end of the slice; `just test-nix` and `just test-scheduled` before the pull
  requests; the judge change (owner's approval) and the work as two pull requests.
- Owner decisions 1 and 2.
