# The aggregates group_concat, string_agg and total (ADR 0015, slice 5)

Created 2026-10-20. Status: open.
Status file: [status](20261020-aggregates.status.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D7.

## Process

As for slices 1 to 4: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **`group_concat(x [, separator])` and `string_agg(x, separator)`** as whole result columns,
   as SQLite 3.51.0's `groupConcatStep` computes them (checked natively):
   - a NULL value is skipped; every other value adds its text (`sqlite3_value_text`: the
     decimal digits of an integer, the 15-digit text of a REAL, the bytes of TEXT and BLOB);
   - each value after the first is preceded by the separator of its own row: `,` without a
     separator argument, nothing for a NULL separator;
   - the values come in the order in which the group sees its rows, which is the scan order
     also with `GROUP BY` (SQLite's sorter keeps the order of equal keys);
   - the result is TEXT, NULL when every value is NULL, and `''` when the values are empty.
2. **`total(x)`**: the REAL sum of `SUM`'s summation (`Summation.lean`, `totalFinalize`):
   `0.0` for an empty group and never an `integer overflow`.

## Tests

- Lean examples of each rule over evaluated groups.
- An authored corpus (`conformance/authored_aggregates.py`), each case with a kernel proof,
  recorded as a new corpus: values of each type, separators per row and NULL, empty and
  all-NULL groups, `GROUP BY` order, and `total` with integers that overflow.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a separator taken from the first row, `group_concat` that keeps NULL values as
  empty text, and `total` that gives NULL for an empty group; each killed by an authored case.

## Key points

- **Files.** `Resolution/ResolvedExprForm.lean` (`Aggregate`), `QueryEval.lean`
  (`Aggregate.eval`), `QueryRun.lean` (`Output.operands`), `Resolution/ExprForms.lean`
  (`aggregateNamed`, `pairAggregateNamed`), `Summation.lean`.
- **Two operands.** `group_concat` has a form with one operand and one with two; the catalog
  checks the number of arguments before resolution picks the form.
