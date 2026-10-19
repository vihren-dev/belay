# Status: collations (ADR 0014, slice 3)

Created 2026-10-19. Status: open.
Task file: [task](20261019-collations.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D3.

## Relevant files

- Values: `packages/belay-sqlite/Belay/Sqlite/Comparison.lean`, `QueryEval.lean`,
  `LiteralData.lean`.
- Resolution: `Resolution/QueryForm.lean`, `Resolution/QueryExprs.lean`,
  `Resolution/Queries.lean`, `Resolution/JoinUsing.lean`, `Resolution/Keys.lean`,
  `Resolution/IndexTerms.lean`, `Resolution/Definitions.lean`.
- Frontend: `belay/sqlite/syntax_definitions.py`, `syntax_queries.py`.
- Harness: `conformance/native_metadata.py`, `conformance/predict_render.py`.

## Progress

- 2026-10-19: native behaviour checked with 3.51.0: `RTRIM` removes trailing spaces before
  a binary comparison (`'a '` < `'a\t'`), so every collation is a total order;
  `NOCASE` folds ASCII only; ORDER BY, `=`, GROUP BY and `min`/`max` over a `NOCASE`
  column use it; `COLLATE BINARY` on the right operand overrides the left column's
  collation; an unknown name is `no such collation sequence: FOO`.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
