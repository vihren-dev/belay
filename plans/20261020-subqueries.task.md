# Subqueries (ADR 0018, slice 1)

Created 2026-10-20. Status: open.
Status file: [status](20261020-subqueries.status.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D1.

## Process

As for ADR 0015: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **Forms.** `EXISTS (q)`, `NOT EXISTS (q)`, `x IN (q)`, `x NOT IN (q)` and the scalar
   subquery `(q)`, in every place where the model evaluates an expression of a query:
   result columns, `WHERE`, `ON`, `GROUP BY`, `ORDER BY` and the arguments of functions,
   and in the `WHERE` and `SET` of `UPDATE` and `DELETE` and the values of `INSERT`. The
   subquery is any `SELECT` that the model resolves, and it may read the columns of the
   queries around it (correlated), as SQLite 3.51.0 resolves names: first in its own
   query, then outward.
2. **Values, as SQLite computes them** (checked natively): `EXISTS` is 1 or 0; a scalar
   subquery is the first column of its first row, or NULL without a row; `IN` follows
   SQLite's affinity and NULL rules for a subquery (the result is NULL when no row matches
   and the subquery gives a NULL). A subquery with more than one column where one is needed
   is SQLite's prepare error.
3. **Faults.** A failure inside a subquery follows the rules of `Fault`: SQLite evaluates a
   subquery only when it needs its value, so its failures are `may` unless the model shows
   that SQLite certainly evaluates it.
4. **Restrictions.** A subquery in `FROM` (a derived table), a compound `SELECT`, and any
   form whose order of evaluation the model does not describe stay restrictions, each with
   its own id and message.

## Tests

- Lean examples of each form over small databases, with kernel proofs.
- An authored corpus (`conformance/authored_subqueries.py`), each case with a kernel proof,
  recorded as a new corpus: each form, correlation at depth one and two, aggregates inside
  a subquery, `IN` with NULLs and with affinity, subqueries in writes, and the prepare
  error of a subquery with two columns.
- The verdict of every corpus: cases that newly agree and none that leave AGREE; the
  kernel time of the corpora's proofs before and after the slice.
- Mutants: `NOT IN` that ignores a NULL in the subquery, a correlated reference read from
  the inner row instead of the outer one, and a scalar subquery that gives its last row;
  each killed by an authored case.

## Key points

- **Syntax is a tree, resolution lifts it to a list.** `Syntax.Expr` holds a subquery's
  syntax, so the syntax types become one mutual inductive type (they need `BEq`, `Repr`
  and JSON, not decidable equality). Resolution gives the statement a list of resolved
  subqueries, and a resolved expression names one by its index, as ADR 0018 decides; a
  subquery's expressions name only later subqueries.
- **Outer cells come first.** A subquery's row is the outer row followed by its own cells,
  so a correlated reference is a cell position; resolution shifts the positions.
- **Evaluation is stratified.** `Expr.evaluate` takes the results of the subqueries as a
  function, and the results at nesting depth n use the evaluation at depth n - 1, with
  fuel, so the recursion stays structural and the kernel reduces it.
- **Files.** `Resolution/SyntaxExpr.lean`, `Resolution/ResolvedExprForm.lean`,
  `Resolution/QueryExprs.lean`, `Resolution/Queries.lean`, `ExprEval.lean`,
  `QueryEval.lean`, `QueryRun.lean`, `QueryFunctions.lean`, the writes that evaluate
  expressions, `Codec/Resolution.lean`, and the frontend `belay/sqlite/syntax_*.py`.
