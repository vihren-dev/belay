# Status: the aggregates group_concat, string_agg and total (ADR 0015, slice 5)

Created 2026-10-20. Status: open.
Task file: [task](20261020-aggregates.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D7.

## Progress

- 2026-10-20: SQLite 3.51.0's `groupConcatStep`, `groupConcatFinalize` and `totalFinalize`
  read; native: the rows of a group keep their scan order with `GROUP BY`, and the separator
  is that of each row (`string_agg(v, w)` is `b2a1c`).

- 2026-10-20: the aggregates ("group_concat, string_agg and total").
  - Lean: `Aggregate.groupConcat` (an optional separator) and `Aggregate.total`;
    `concatText`, `concatSeparator`, `concatRows`, `groupConcatValue` in `QueryEval.lean`;
    `SumState.totalValue`; the names in `aggregateNamed` and `pairAggregateNamed`;
    `Functions/AggregateExamples.lean`. `QueryResolutionExamples` uses `median` as the
    aggregate that the model does not describe.
  - `conformance/authored_aggregates.py`: 3 cases, all agree; `aggregate_evidence.py`
    (corpus 40); `aggregate_mutants.py`, all killed. The task's first mutant is now a separator
    argument that is ignored (amended).
  - Tests run: `function_catalog`, `test_model_package`, `mutant_guards`,
    `conformance_authored`, `conformance_predict`, `test_lean_categories`,
    `conformance_query_coverage`, the aggregate mutants.

## Remaining

- Review, the slice verdict, corpus 40, `just test-full`.
