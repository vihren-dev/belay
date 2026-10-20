# The exact numeric functions (ADR 0015, slice 2)

Created 2026-10-20. Status: open.
Status file: [status](20261020-numeric-functions.status.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D4.

## Process

As for slice 1: local jj commits with the tests that touch each one; at the end of the slice
the local verdict, the corpus, and `just test-full`. The pull requests come at the end of the
ADR.

## Outcome

1. **Functions.** `round(x [, digits])`, `floor`, `ceil`, `ceiling`, `trunc`, `sqrt`, `pi`,
   `degrees`, `radians` and `mod` resolve to `Resolved.Expr.scalar` and follow SQLite 3.51.0's
   `func.c`, checked natively:
   - `floor`, `ceil` and `trunc` keep an integer (also text that reads as an integer) as an
     integer, give a REAL for a REAL, and NULL for anything else; the result of a REAL keeps
     the sign of zero (`trunc(-0.5)` is `-0.0`);
   - `round` gives a REAL: a value beyond 2^52 stays, zero digits add or subtract 0.5 and
     truncate, other digits write the value with `%!.Nf` and read it back; the digits are
     clamped to 0 to 30, and NULL digits or a NULL value give NULL;
   - `sqrt`, `degrees`, `radians` and `mod` read a number (or text that reads as one) as a
     double and give a REAL, NULL for another value; `sqrt` of a negative number and `mod`
     with a zero divisor are NULL, as SQLite stores no NaN;
   - `pi()` is the double nearest to π.
2. **Exact.** Each result is the one that the C library gives for these exact operations, so
   it does not depend on the platform: `sqrt` and the products and quotients of `degrees` and
   `radians` are IEEE operations, `floor`, `ceil` and `trunc` round to an integer, and `mod` is
   the exact remainder (`fmod`). The kernel reduces each of them.
3. **Not here.** The transcendental functions (`ln`, `log`, `exp`, `pow`, the trigonometric
   and hyperbolic functions) stay `unmodeled-function`.

## Tests

- Lean examples of each function, with the sign of zero, large values and the NULL cases.
- An authored corpus (`conformance/authored_numeric_functions.py`), each case with a kernel
  proof, recorded as a new corpus.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: `round` that rounds half to even, `floor` that truncates toward zero, and `mod`
  that keeps an integer result, each killed by an authored case.

## Key points

- **Files.** `Functions/Scalar.lean` (`ScalarFunction.apply`), a new numeric module,
  `Resolution/FunctionCalls.lean` (`scalarCall`), `RealText.lean` (`decodeDouble`,
  `fixedDigitBytes`) for the `%!.Nf` of `round`.
- **Kernel.** The kernel reduces `Float` addition, multiplication, division, `sqrt`,
  `toInt64` and `ofInt`, but not `floor`, `ceil`, `round` or `fmod`; these are written with the
  integer conversion below 2^52 and with exact integer arithmetic on the bits for `mod`.
- **Numeric type.** `sqlite3_value_numeric_type` is SQLite's numeric affinity of the argument:
  text that reads as a number becomes that number (`numericText`).
