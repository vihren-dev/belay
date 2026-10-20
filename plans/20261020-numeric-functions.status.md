# Status: the exact numeric functions (ADR 0015, slice 2)

Created 2026-10-20. Status: open.
Task file: [task](20261020-numeric-functions.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D4.

## Progress

- 2026-10-20: native facts checked with 3.51.0: `floor(3)` is an integer, `floor('3.7')` is
  3.0 and `floor('x')` NULL; `trunc(-0.5)` and `ceil(-0.5)` are `-0.0` (written `0.0`);
  `round(2.5)` 3.0, `round(-2.5)` -3.0, `round(1.005, 2)` 1.0, `round(-0.001, 2)` `-0.0`;
  `sqrt(-1)` and `mod(1, 0)` are NULL; `mod(7, 3)` is 1.0 and `mod(-7, 3)` -1.0.

- 2026-10-20: the functions, examples, corpus writer and mutants (commit "exact numeric
  functions").
  - Lean `Functions/Numeric.lean`: `truncDouble`, `floorDouble`, `ceilDouble` (the integer
    conversion below 2^52 and the sign of zero), `roundValue` (with `fixedText` for
    `%!.Nf`), `doubleValue`, `piDouble`, and `modDouble` (the exact remainder from the bits,
    with `decomposeDouble` and `composeDouble`).
  - Native: the recorder keeps the bits of `-0.0`, and the model gives the same bits.
  - `conformance/authored_numeric_functions.py`: 9 cases, all agree with kernel proofs;
    `numeric_function_evidence.py` (corpus 37); `numeric_function_mutants.py` (round half to
    even, floor that truncates, mod that keeps integers), all killed.
  - Tests run: `test_model_package` (160 modules), `mutant_guards`, `restriction_registry`,
    the kernel proofs and corpus writer of corpus 37, the numeric mutants.

## Remaining

- Review, the slice verdict, corpus 37, `just test-full`.
