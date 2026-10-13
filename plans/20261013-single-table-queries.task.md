# Single-table queries, slice 1 of ADR 0012

Created 2026-10-13. Status: DONE (pull requests #107 and B).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Decision" for the
first slice (levels, syntax and resolution, values, expressions, queries, output,
statements, testing). Related: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md)
for the layering, [ADR 0005](../docs/adr-0005-conformance-corpus-scale.md) section
3.1 for output comparison, ADR 0011 for claims.

## Plan

Two pull requests, as for step 2b of ADR 0008:

- **Pull request A (subject):** syntax, resolution with its specification, the
  Values, Expressions and Queries levels with their proofs, query outputs in
  the execution semantics, the frontend mapping, model cases, authored coverage
  cases, mutants and their corpus writer. No change under `judge/` or
  `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus is frozen and
  claimed, and the agreeing corpus cases with queries are claimed.

## Outcome

1. **Syntax.** `Syntax.Statement.select` with result columns (`*`, or an
   expression with an optional alias and its source text), one table, an
   optional `WHERE`, `GROUP BY` terms, `ORDER BY` terms with direction, and
   optional `LIMIT` and `OFFSET`. `Syntax.Expr` gains the comparison operators,
   `IS`, `IS NOT`, `IS NULL`, `IS NOT NULL`, `AND`, `OR`, `NOT`, and the
   aggregates `COUNT(*)`, `COUNT(x)`, `MIN(x)` and `MAX(x)`. The frontend maps
   these forms and keeps refusing others.
2. **Resolution.** `resolve` gives `Resolved.query`, or the prepare errors of
   ADR 0012 (`no such column`, `misuse of aggregate function`, `ORDER BY` and
   `GROUP BY` terms out of range), or a model restriction for the forms that the
   ADR lists. Each new rule has a declarative statement and a proof.
3. **Values.** SQLite's comparison: storage-class order, exact integer-real
   comparison, BINARY text, affinity before a comparison, NULL and
   three-valued logic, with a proof that the order is a total preorder.
4. **Expressions and queries.** Evaluation against a row; the query steps of
   ADR 0012 (source, filter, groups, projection, order, window), with the proofs
   that the ADR lists (filter, sorted permutation, window length, count).
5. **Statements.** A query has no state effect; its output is the result column
   names and rows, with no change count; the verification target is unchanged.
6. **Evidence.** Native model cases with queries agree and have kernel proofs;
   authored coverage cases for each rule, with neighbors; the mutants of ADR
   0012 each change a verdict; the verdict counts of the claimed corpora do not
   go down.

## Tests

- Frontend mapping of each new form, the source text of result columns, and
  refusal of the forms outside the slice.
- Lean examples and specification proofs of resolution and of the semantics.
- Model cases and coverage cases, compiled and kernel-proved; the mutants.
- The prediction path produces query outputs that the judge compares; the
  verdict passes.

## Key points for the implementer

- A function-call constructor with a `List Expr` argument makes `Syntax.Expr` a
  nested inductive type: the `induction` in `Resolution/ErrorKinds.lean` and the
  structural recursion of `literalValue` and `constantDefault` do not support
  it. Give the aggregates their own constructors with one argument.
- `Resolved.Statement` has 12 exhaustive match sites (execution, SQL execution,
  proofs, outputs, `prepareError?`); `Syntax.Statement` has 4. A query keeps the
  database: in `advance` it continues with the same state.
- `Resolution/Writes.lean` (170 lines), `NamesSpec.lean` (171) and
  `Resolution/Examples.lean` (176) are near the size limit; query resolution
  and its examples go into new modules.
- Result column names follow ADR 0012, "Output": checked against SQLite 3.51.0
  (`SELECT ABC` on a column `Abc` is named `Abc`; an expression keeps its text
  exactly, as `abc = 1`).
- ADR 0005 compares rows without `ORDER BY`, ties, and `LIMIT` cuts as
  multisets; the judge (`judge/outputs.py`) and `Outputs.lean` already do so.
- The frontend refusal `"SELECT 1;"` in `tests/syntax_mapping_test.py` expects
  the old advice and changes with this slice.
