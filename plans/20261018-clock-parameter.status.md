# Status: the clock is an evaluation parameter (ADR 0013, step 6)

Created 2026-10-18. Status: DONE.
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
- 2026-10-18: `TimeKeyword.value` is the keyword's date and time function without
  arguments (`TimeKeyword.dateFunction`, in `Date/Functions.lean`); the duplicate time of
  day and text functions of `ClockText.lean` are gone, and `ClockText.lean` keeps the
  keywords and the shared `date.c` parts. The natively checked keyword examples hold on
  the new definition (also probed at 15 edge clocks against the old one). Examples: a
  clock-reading `VALUES` item stored with its column's affinity. Verdict unchanged.

- 2026-10-18: all three suites pass on the tip after three test fixes (a RETURNING mutant
  replacement and the generated Lean of three tests). CI time against step 5:
  `tests.harness` 21 s to 23 s, `tests.model` 337 s to 335 s, `tests.frozen` 142 s to
  140 s, scheduled mutants 419 s to 395 s. Pull request #166.

## Remaining

- None. Step 7 of ADR 0013 follows.
