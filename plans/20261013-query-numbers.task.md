# Numbers in queries, slice 2 of ADR 0012

Created 2026-10-13. Status: IN PROGRESS.
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Slices", item 2,
with the levels, testing rules and layering of its "Decision". Related: slice 1,
[task](20261013-single-table-queries.task.md) (done, #107 and #108); ADR 0005
section 3.1 for output comparison; ADR 0011 for claims. The authority for each
rule is the pinned SQLite 3.51.0 source and native SQLite, as in slice 1.

## Plan

Two pull requests, as for slice 1:

- **Pull request A (subject):** syntax, resolution with its specification, the
  number rules of the Values and Expressions levels with their proofs, `SUM` and
  `AVG` in the Queries level, the query failure of `SUM`, the frontend mapping,
  authored coverage cases with kernel proofs, mutants and their corpus writer.
  No change under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus is frozen and
  claimed, and the corpus cases that newly agree are added to `mustAgree`.

## Outcome

1. **Numeric literals.** A REAL literal in a query (`1.5`, `1e3`, an integer
   literal too large for 64 bits) has the value that SQLite's parser gives it.
   REAL literals in `INSERT` and `UPDATE` stay a model restriction (slice 3).
2. **Arithmetic.** `+`, `-`, `*`, `/`, `%` and unary `-` and `+` on query
   expressions, with SQLite's rules: integer arithmetic while both operands are
   integers and the result fits in 64 bits, else REAL; integer division that
   truncates; NULL for division or remainder by zero and for a NaN result; REAL
   `%` through integer conversion; NULL operands give NULL; TEXT and BLOB
   operands convert as SQLite converts them for arithmetic.
3. **`CAST`.** `CAST(x AS type)` for the affinity of any type name, with
   SQLite's conversions between NULL, INTEGER, REAL, TEXT and BLOB, including
   REAL to TEXT (`%!.15g`) and TEXT to a number. A `CAST` expression has the
   affinity of its type in a comparison, as in SQLite.
4. **`COALESCE`.** The first non-NULL argument, with SQLite's prepare error for
   a wrong number of arguments.
5. **`SUM` and `AVG`.** `SUM` gives an integer while every input is an integer
   and the sum fits; else a REAL by the Kahan-Babuska-Neumaier summation of the
   pinned release; NULL over no non-NULL input; and the `integer overflow` error
   when the statement runs. `AVG` gives a REAL, or NULL over no input, and never
   fails.
6. **Failing queries.** A query whose evaluation fails stops the script with
   the step-phase error, as other step errors do. Its state effect is still
   none, and the verification target does not change.
7. **Evidence.** Every new rule has authored coverage cases (a case, a neighbor
   and boundary values) that agree with native SQLite and have kernel proofs;
   mutants for the rules below each change a verdict; the verdict counts of the
   claimed corpora do not go down.

## Tests

- Frontend mapping of each new form, and refusal of the forms outside the
  slice, with byte ranges.
- Lean examples and specification proofs: at least that integer arithmetic that
  fits gives the exact integer result, that `COALESCE` gives its first non-NULL
  argument, that `SUM` over integers that fit is their exact sum, and that the
  conversions of literals agree with SQLite on stated examples.
- Authored coverage cases, compiled and kernel-proved, among them: overflow at
  both 64-bit limits for `+`, `-`, `*` and `/` (`-9223372036854775808 / -1`);
  division and remainder by zero and by `-1`; `inf - inf`; REAL `%`; TEXT
  operands such as `'1.5'`, `' 7 '`, `'1e3'`, `'abc'`; `CAST` of each storage
  class to each affinity, including large REAL to INTEGER and REAL to TEXT with
  15-digit rounding; `SUM` with integers only, with a REAL, with an overflow,
  with an overflow and then a REAL (no error), with only NULL, and over no rows;
  `AVG` of the same inputs; and a REAL literal for which SQLite's conversion
  differs from correct rounding, if one exists.
- Mutants, each changing the verdict of a case: overflow not promoted to REAL;
  `/` on integers computed as REAL; division by zero not NULL; NaN not NULL;
  REAL `%` computed with `fmod`; `SUM` summed naively; the `SUM` overflow error
  removed; `AVG` as an integer; `CAST` to INTEGER that rounds; `COALESCE` that
  returns its last non-NULL argument; text conversion that ignores spaces or
  exponents; and the `COALESCE` argument-count error removed.
- The prediction path produces the new outputs and the failure that the judge
  compares; the verdict passes.

## Key points for the implementer

- **REAL in the kernel.** In the pinned Lean (4.34.1), `Float` is a Lean model
  (`Float.ofModel`) that the kernel evaluates with IEEE rounding: `decide
  +kernel` proves `(0.1 + 0.2).toBits = 0x3FD3333333333334` and `(7 / 3).toBits`.
  `Value.real` holds the IEEE bits; use `Float.ofBits` and `Float.toBits`. Check
  the kernel cost of long `Float` computations early, as the cost of
  `String.map` surprised slice 1.
- **SQLite's own conversions are not correctly rounded.** Text to REAL is
  `sqlite3AtoF` (amalgamation line 36396), and REAL to text is `%!.15g` through
  `sqlite3FpDecode` (36884, used by `vdbeMemRenderNum`, 84857). Both use
  Dekker double-double steps. A port must follow them step by step;
  `Float.ofScientific` is correctly rounded and can differ.
- **Arithmetic** is `OP_Add` to `OP_Remainder` (97176): the `-1` divisor rules,
  `fp_math` after an integer overflow, NaN to NULL, and REAL `%` through
  `sqlite3VdbeIntValue`. TEXT and BLOB operands go through `numericType`.
  `sqlite3RealToI64` (85518) converts REAL to INTEGER.
- **`SUM` and `AVG`** are `sumStep`, `sumFinalize` and `avgFinalize` (133601 to
  133760): an integer input that overflows switches to the approximate sum and
  sets the overflow flag; a later REAL input clears the flag; large integers
  enter the approximate sum in two parts. `AVG` uses the same context without
  the error. `sqlite3_value_numeric_type` converts TEXT inputs.
- **A query can now fail.** `step` returns `.success` for a query today, and
  `Outputs.statementOutput` returns its rows. The `SUM` error must use the
  existing step-failure path with the step phase. It is not a model restriction
  (R7).
- **Nested inductive types.** A call with a list of arguments makes
  `Syntax.Expr` nested (see the slice 1 task). `COALESCE` needs at least two
  arguments; give it a form that keeps `Syntax.Expr` and `Resolved.Expr` plain
  inductive types.
- **Affinity.** Slice 1 restricts comparisons whose affinity rule would convert
  a value (`Resolution/QueryExprs.lean`, `conversion`). An arithmetic result has
  no affinity, and a `CAST` has the affinity of its type; the restriction rules
  must take both into account.
- **Literals.** `NumericValue.real` (`Resolution/Values.lean`) has no value
  today, and every REAL literal is restricted. Queries need the value; writes
  keep the restriction.
- **Mutant build.** `#guard` examples in a module of the import closure of
  `VerifierConformance.Case` stop mutant builds (slice 1 moved the comparison
  examples to `QueryExamples.lean`). Keep examples in separate modules.
- **File size.** `QueryEval.lean` (131 lines), `QueryLaws.lean` (156) and
  `Resolution/QueryExprs.lean` (168) are near the limit; put number rules in new
  modules.
