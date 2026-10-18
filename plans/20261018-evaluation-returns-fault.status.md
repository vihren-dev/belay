# Status: evaluation returns its fault (ADR 0013, step 3)

Created 2026-10-18. Status: open.
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

## Remaining

- Implementation, full checks, verdict measurement, review, CI time, pull request A.
