# Status: evaluation returns its fault (ADR 0013, step 3)

Created 2026-10-18. Status: DONE.
Task file: [task](20261018-evaluation-returns-fault.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D2.

## Relevant files

- Evaluation: `packages/belay-sqlite/Belay/Sqlite/QueryEval.lean`, `QueryJoins.lean`,
  `QueryFunctions.lean`, `Json/JsonApply.lean`.
- Predictors to remove: `JsonFaults.lean`, `JsonReady.lean`; uses in `Execution.lean`
  (`step`), `StatementStep.lean` (`statementReady`), `Resolution/Assignments.lean`,
  `Resolution/ClockRows.lean`, `SqlProofs.lean` (`NoWrites`, `supportedSqlFrom_noWrites`),
  `Laws.lean` (`literal_cases`).
- Readiness: `LiteralData.lean`, `RowUpdate.lean`, `UpsertRun.lean`.
- Classifier: `packages/verifier-conformance/VerifierConformance/Case.lean`, `Predict.lean`,
  `Outputs.lean`, `Trace.lean`.
- Examples: `JsonFaultExamples.lean`, `QueryExamples.lean`.
- Mutants: `conformance/json_mutants.py`, `number_mutants.py`, `query_mutants.py`,
  `row_write_mutants.py`, `write_mutants.py`, `obligation_mutants.py`.

## Progress

- 2026-10-18: code map done (the fault rules, the readiness reruns, the three classifier
  passes and the resolver's use of the predictors).

- 2026-10-18: `Expr.evaluate` gives a value and a `Fault`; `Expr.eval` is its value.
  `QueryRun.lean` replaces `JsonFaults.lean`: `Query.run` gives rows, fault and
  overflow, and the query fault rules are stated over `evaluate`. `Expr.any` and
  `Expr.isJsonCall` (`Resolution/ExprAny.lean`) replace `callsJson`. Every fault
  example keeps its result. The three suites pass; the review is clean.
- 2026-10-18: `passFrom` (`VerifierConformance/Pass.lean`) is the one classifier pass,
  with `passFrom_final` and `passFrom_supported`. The model suite: 326 s (335 s
  before). Outcome 4 is deferred by that measurement (task file).

- 2026-10-18: the three suites pass on the tip (the model inputs of
  `build-support/tests.nix` gained `Pass.lean`). Both reviews are clean. The verdict
  counts and report equal step 2's. CI time against step 2: `tests.harness` 22 s to
  22 s, `tests.model` 335 s to 332 s, `tests.frozen` 140 s to 140 s, scheduled mutants
  411 s to 412 s.

- 2026-10-18: pull request #161, stacked on #160.

## Remaining

- None. Steps 4 and 5 follow; they change verdicts and are measured first.
