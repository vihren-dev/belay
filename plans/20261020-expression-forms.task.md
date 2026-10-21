# The expression forms IN, BETWEEN, CASE and || (ADR 0018, slice 2)

Created 2026-10-20. Status: DONE (2026-10-21).
Status file: [status](20261020-expression-forms.status.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D2.

## Process

As for slice 1: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **`x IN (a, b, ...)` and `x NOT IN (...)`**, also with an empty list, in every place
   where the model evaluates an expression of a query or a write. The value follows the
   matrix of `IN` (as for a subquery in slice 1): an empty list gives 0 (`NOT IN`: 1), also
   for NULL; else a NULL operand gives NULL; a value that compares equal gives 1; else a
   NULL in the list gives NULL; else 0.
2. **`x BETWEEN a AND b` and `x NOT BETWEEN a AND b`**, as `x >= a AND x <= b` with `x`
   evaluated once, where each comparison has the affinity and collation rules of `>=` and
   `<=`.
3. **`CASE`** with and without a base expression, with and without `ELSE`. With a base,
   each `WHEN` value is compared with the base as `=` compares them; a NULL base matches no
   `WHEN`. Only the branch that SQLite takes is certain to run, so the faults of the others
   are softened, as for `iif`.
4. **`x || y`**: NULL when an operand is NULL, else the text of both operands, each as
   `concat` writes it.

## Tests

- Lean examples of each form and its NULL rules, with kernel proofs.
- An authored corpus (`conformance/authored_expression_forms.py`), each case with a kernel
  proof, recorded as corpus 43: each form in a result column, in `WHERE` and in a write;
  the affinity and collation rules of the `IN` list, of `BETWEEN` and of `CASE` with a base;
  the NULL matrix of the `IN` list; the text of integers, REAL values and BLOBs in `||`.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: an `IN` list whose values compare under the collation of a column on the right, `BETWEEN` that gives NULL when either comparison is NULL, before it checks whether the other comparison is false (a false lower bound with a NULL upper bound must give 0), `CASE` whose NULL
  base matches a NULL `WHEN`, and `||` that skips a NULL operand as `concat` does; each
  killed by an authored case.

## Key points

- **The affinity and collation of an `IN` list come from its left operand.** SQLite's parser
  rewrites `x IN (c)` with one constant value `c` into `x = +c` (`NOT IN`: `NOT` of it),
  and a list of one parenthesized subquery into `x IN (SELECT ...)`. Every other list
  compares each value under the affinity of `x` (`exprINAffinity`) and the collation of `x`
  (`sqlite3ExprCollSeq` of the left operand, in both `sqlite3ExprCodeIN` and the key of the
  ephemeral index of `sqlite3CodeRhsOfIN`). Checked natively over
  `t(i INTEGER, s TEXT, n TEXT COLLATE NOCASE)` with the row `(1, '1', 'A')`: `i IN ('1')`,
  `i IN ('1', 'x')`, `i IN (s)` and `n IN ('a', 'b')` are 1; `'a' IN (n, 'z')` is 0;
  `n IN ('a' COLLATE BINARY)` is 0 (rewritten to `=`, whose explicit right collation
  decides), but `n IN ('a' COLLATE BINARY, 'b')` is 1.
- **`CASE` with a base compares as `=`.** Natively, `CASE '1' WHEN i THEN ...` matches
  (the comparison affinity of both sides) and `CASE 'a' WHEN n THEN ...` matches (the column
  collation of the `WHEN` side), unlike the `IN` list.
- **`BETWEEN` gives NULL and 0 as `AND` does.** `1 BETWEEN NULL AND 2` is NULL, and
  `3 BETWEEN NULL AND 2` is 0.
- **The text of a REAL in `||`** is SQLite's `%!.15g` form, as `CAST(x AS TEXT)` gives it:
  `1e300 || ''` is `1.0e+300`, `-0.0 || ''` is `0.0`, `100.0 || ''` is `100.0`.
- **Files.** `Resolution/SyntaxExpr.lean` and the frontend `belay/sqlite/syntax_queries.py`
  (new syntax forms), `Resolution/ResolvedExprForm.lean`, `Resolution/QueryExprs.lean`,
  `ExprEval.lean` (with `inValue` of slice 1), and every exhaustive match over the syntax
  and resolved expression types, as in slice 1.
