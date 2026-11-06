# Compositional SELECT proofs: task status

Date: 2026-11-07. Status: IN PROGRESS (slice 1).
Audience: the implementation team.
Task: [Compositional SELECT proofs](20261107-select-phase-rules.task.md).
Specification: [ADR 0027](../docs/adr-0027-compositional-select-proofs.md),
[acceptance contract](../docs/select-automation-acceptance.md),
[retirement inventory](../docs/select-automation-retirement.md).
Source baseline: the accepted specification on bookmark
`spec/adr-0027-compositional-select-proofs` (PR 299, `7e799755`, on main `c54d8395`).

Relevant files: `tests/surface/SelectAutomation*.lean` (experiments),
`packages/belay-sqlite-model/Belay/Sqlite/Model/QueryResults.lean`,
`Model/QueryOutputFacts.lean`, `packages/belay/Belay/Sqlite/Queries.lean`,
`Belay/Sqlite/ReadStepRule.lean`, `Belay/Sqlite/SqlRun.lean`, `Belay/Sqlite/AutoSearch.lean`.

## Progress

- 2026-11-07: task specified (review `20261106T221739Z-b9ad0060`).
- 2026-11-07: review fixes (`refactor:`): the task file states outcomes without an
  order; the working sequence and the candidate decisions are in this file;
  `ColumnQuery.lean` retires after A19.

## Working sequence

Each stage ends with the checks of a slice end (`just test-full`, `just verdict`).

1. Execution rule, `Run.returnsResult`, `Run.returnsRows` and `Run.returnsError` with
   their bridges, the `Holds`/`Empty`/`Fails` abbreviations; projection, filter and
   expression rules; A01 to A04, A11, B01, B02, B05, B11; retirement of
   `SelectOneFrom`, the `Simple*` laws and the outputs that only these cases cover.
2. Group, aggregate, HAVING, DISTINCT, order and window rules; A07 to A10, A12 to
   A14; retirement of the count, aggregate and duplicate-key families.
3. Source, join, compound, subquery and context rules; A05, A06, A15 to A22;
   retirement of `ColumnQuery`, `UniqueLookupQuery`, the EXISTS, no-FROM, may-fail,
   query-case and hint families.
4. `sql_select`, `sql_select_rule`, the `sql_run` delegation and the `sql_auto`
   route; automatic closure of the core set; B03, B04, B06 to B10; the end-to-end
   theorems; deletion of the experiments and migration witnesses; the measurement.

## Candidate decisions (at assignment, 2026-11-07)

- `TableInfoQuery.lean` and `Model/TableInfoOutput.lean`: delete. The only consumer of
  `Script.outputOn_tableInfo` is `tests/surface/ClaimsTableInfo.lean`, which moves to
  the pragma source rule of A20. `Resolved.Query.source_pragma_fixed`, a general
  source law used by `tests/surface/SuccessBalanceSubqueries.lean`, moves to the
  source rules first.
- `InSubquery*` (eight model files): retain. `NotInQuery.lean` (ADR 0026 D4) uses
  `resolvedStepOutput_in_eq_exists_of_rowidAlias` and
  `resolvedStepOutput_notIn_eq_notExists_of_rowidAlias` of
  `InSubqueryQueryRowidAlias`, whose import chain contains the other seven files.
  A declaration of the chain that this consumer does not use is deleted when the
  `subquery` rule exists.
- Model examples: `QueryExamples` stays (the conformance package
  `VerifierConformance/QueryOutputs.lean` imports it). In `SubqueryExamples`,
  `QueryWindowExamples`, `PossibleResultsExamples` and `InSubqueryExamples`, an
  example that an acceptance contrast repeats is deleted when that contrast lands;
  an example that protects a boundary that no case covers stays, and this file
  names it.
