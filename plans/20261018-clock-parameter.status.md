# Status: the clock is an evaluation parameter (ADR 0013, step 6)

Created 2026-10-18. Status: open.
Task file: [task](20261018-clock-parameter.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D6.

## Relevant files

- Clock: `packages/belay-sqlite/Belay/Sqlite/ClockText.lean`, `ClockSubstitution.lean`,
  `StatementClock.lean`, `StatementClockLaws.lean`, `SchemaClock.lean`,
  `SqlExecution.lean`, `Resolution/ClockCell.lean`, `ClockRows.lean`, `ClockRowRules.lean`.
- Evaluation: `ExprEval.lean`, `QueryEval.lean`, `QueryRun.lean`, `QueryJoins.lean`,
  `QueryFunctions.lean`, `JsonReady.lean`, `Execution.lean`, `StatementStep.lean`,
  `RowUpdate.lean`, `RowDelete.lean`, `Upsert.lean`, `UpsertRun.lean`.
- Date: `Date/Functions.lean`, `Date/Parse.lean`, `Date/DateTime.lean`.
- Harness: `packages/verifier-conformance/VerifierConformance/Case.lean`, `Predict.lean`,
  `Outputs.lean`.
- Users of the clock lemmas: `packages/sqlite-verifier/SqliteVerifier/ContractProofs.lean`,
  `FailureDemonstration.lean`, `ApplicationKeyDemonstration.lean`,
  `examples/constant_default/Proofs.lean`, `examples/missing_required_column/Proofs.lean`,
  `examples/atuin/Proofs.lean`.

## Progress

- 2026-10-18: code map. The clock reaches the date functions only through
  `DateTime.current` (`parseDateOrTime` for `now`, `subsec`, `subsecond`, and no
  argument). The approved files and `Contract.lean` use none of the changed names.
- 2026-10-18: the clock is an evaluation parameter. `Expr.evaluate`, the query, join and
  write functions, `step`, `literalStep` and `statementReady` take the clock value;
  `SqlState.clock` is the clock assignment, and `advance` passes the value of its
  position. `runSqlAt` runs with `scriptClock`: the assignment's value for a statement
  that reads the clock, else 0, so the one-outcome lemma for a script without clock reads
  follows from the gate, not from a congruence proof over every execution function.
  `ClockReads.lean` (classifier with `Expr.any`; `namesClock` now cuts at NUL, as
  `parseDateOrTime` does) replaces `ClockSubstitution.lean`; `StatementClockLaws.lean`,
  the `atClock` family and `scriptAtClock` are gone. A clocked INSERT is filled at step
  time (`Statement.unclock`). The harness runs the gated assignment. Verdict unchanged,
  entry for entry.
- 2026-10-18: review of the clock commit: four "must" findings (a NUL time value test,
  clock quantifiers in five plain-words statements, a proof sketch), fixed in a
  `refactor:` commit; its review is clean.
- 2026-10-18: INSERT rows are rows of `Resolved.Cell`: a stored value, or an expression
  that reads the clock, which `literalStep` evaluates at the statement's clock value and
  stores (`Cell.valueAt`, `rowsAt`). `Statement.clocked`, `ClockCell`, `ClockRows.lean`
  (now `InsertCells.lean`) and `ClockRowRules.lean` (now `InsertCellRules.lean`) are gone;
  `RowWidth` is stated over cells. The core has 134 modules. Verdict unchanged.

## Remaining

- Time keywords through the date functions and the `ClockText` duplicates; examples.
- Full checks, verdict comparison, review, CI time, pull request.
