# Status: parameters (ADR 0019, slice 1)

Created 2026-10-23. Status: open.
Task file: [task](20261023-parameters.task.md).
Specification: [ADR 0019](../docs/adr-0019-guide-sql.md), D1 (amended 2026-10-23).

## Progress

- 2026-10-23: ADR 0019 D1 amended (owner decision 4): a corpus case binds the values that its
  trace records for each statement.
- 2026-10-23: the task file, from native probes (3.51.0, typed bindings) and the measurement of
  the out-of-scope cases with a parameter.
- 2026-10-23: the model's expressions (commit "feat: parameters in the model's expressions"):
  `Syntax.Expr.parameter` and `Resolved.Expr.parameter`, the values in `EvalContext`, no
  folding in VALUES cells and SET values, `ORDER BY ?` and `GROUP BY ?` as values, and
  SQLite's prepare errors of outcome 6. `PrepareError` moved to `StatementPrepareError.lean`.
  `just test-full` passed.
- 2026-10-23: review rounds 1 to 3 had must findings (R7), all on the order of the error of a
  prohibited parameter against the other errors of SQLite's walk of names. Native probes
  showed that SQLite's walk keeps the last error, that a parameter, a missing name and a
  subquery stop it, that a function call's arguments and the operand of ISNULL end the stop,
  that a compound node after an error stops before its operands, that function errors and
  `.` in generated columns are errors of the walk, and that `x AND 0` and `x IN ()` lose
  their operands at parse. Two refactor commits modeled more of the walk, and each review
  found more of it. The third fix stops the emulation: the model gives the parameter's error
  only where it is the only error that the walk can find (`ParameterOrder.lean`), and the new
  restriction `parameter-error-order` everywhere else. The task file's outcome 6 says so.
- 2026-10-23: the restriction needs an example through the frontend, so the third fix also
  has the frontend's numbering (C2): `Translation/Parameters.lean` numbers the `VARIABLE`
  tokens of each command by their bytes before the translation, and refuses `?0`, numbers
  above 32766, too many numbers and `#1` with SQLite's messages (`INPUT_ERROR`; the task
  file's outcome 2 says so). `DEFAULT (?)` reaches the model. Frontend tests:
  `tests/syntax_parameters_test.py`. Corpus cases that bind values stay out of scope until C3.
  `just test-full` passes (463 and 155 tests); `tests/conformance_model_test.py` now checks
  that a case with bound values prepares and that the model's run gives MODEL_UNSUPPORTED.
