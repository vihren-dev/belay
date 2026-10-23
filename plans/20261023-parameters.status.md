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
- 2026-10-23: review round 4 of the fix: no must findings. Its two should findings are fixed
  in a refactor commit: the restriction's message names the forms that SQLite removes before
  it resolves names, and the task file says that the frontend refused parameters before this
  task. `just test-full` passes.
- 2026-10-23: the bound values reach evaluation (C3). Each statement of a run carries its
  values as a pair `(statement, values)`: the model's script and SQL runs, the surface's
  `Script.statements` (new primitive `Script.withValues`; `sql "..."` binds no values), and
  the conformance pass, which gives statement i the case's recorded values i. Subqueries see
  the values of their statement; trigger bodies get none. The guards that refused cases with
  bound values are removed, and six authored cases that bind values now agree. The values
  are not in the state, so the append laws keep their form; each changed law holds for all
  values. `TableExtensionLaws.lean` takes two laws from `PreservationLaws.lean` (200 lines).
  `LIMIT ?` stays refused until C4. `just test-full` passes (463, 146 and 155 tests).
- 2026-10-23: review of C3: a bound NaN REAL is NULL, as SQLite binds it (`boundValue`); the
  plain words of the changed laws are complete. The next review had no findings.
- 2026-10-23: owner decision: `just review` runs before `just test-full`; the full test runs
  once after the review rounds.
- 2026-10-23: `LIMIT ?` and `OFFSET ?` (C4). A lone parameter resolves to the query's new
  fields `limitParameter` and `offsetParameter`; `Query.run` binds the window when the query
  starts (`QueryWindow.lean`): LIMIT first, OFFSET only when the LIMIT is not 0, each through
  `numericStore` to an integer, else `datatype mismatch` (`QueryRun.mismatch`). The bound
  query has literal fields, so the readers of the window and their laws do not change. In a
  subquery a mismatch is a `may` fault. The case `numeric-ties-windows` is expected to agree;
  the Nix verdict is pending. Kernel examples of each value of outcome 5 are in
  `QueryWindowExamples.lean`.
- 2026-10-23: the authored corpus of parameters (C5), in `conformance/authored_parameters.py`
  and its two case modules: 44 cases, recorded natively, each in the kernel-proof coverage
  set, with the writer of corpus version 48 (`parameter_evidence.py`). The coverage needs
  every case to agree, so the cases leave out `INSERT ... SELECT` (not modeled), `GROUP BY` of
  an expression (restriction `group-by-term`) and the example of `parameter-error-order`,
  which `restriction_examples.py` has; `DEFAULT ?` without parentheses is a frontend test.
  The native recorder sets two limits: a sort key must be a result column, so
  `parameter-order-by` also selects `?1`, and a subquery's own window is not recorded.
  Mutants (`parameter_mutants.py`): a parameter with an affinity, `ORDER BY ?` as a column
  number and a `LIMIT ?` that truncates a fraction, each killed by an authored case. The two
  numbering mutants change the frontend, which the mutant measurement does not build, so no
  check shows yet that a case kills them. Open: a check of the two numbering mutants (owner
  decision); corpus-v48 and its claims are the judge change (owner).
