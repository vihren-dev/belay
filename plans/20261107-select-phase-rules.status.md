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
- 2026-11-07: review fix (`refactor:`): a decision for each model example file.
- 2026-11-07: run observations of D2. `Output.returnsResult` and `Output.returnsError`
  (`Model/QueryOutputs.lean`), `Run.returnsResult`, `Run.returnsRows` and
  `Run.returnsError` (`RunResults.lean`), each decidable by a term that the kernel
  reduces. `Run.returnsError` is the "matching error observation" of D2 that `Fails`
  needs. A SELECT step that continues the run gives rows, an error or a choice of at
  least two results (`Model/SelectOutputShape.lean`); a step that ends the run gives no
  value, which no claim accepts. So the bridges to `Sql.check` (`RunResultSteps.lean`,
  `SelectResultBridge.lean`, `SelectErrorBridge.lean`) hold for raw and concrete choices
  without a vacuous empty choice. `Holds`, `Empty` and `Fails` are abbreviations of the
  observations of the default run; `QueryObservations.lean` relates them to
  `Script.outputOn`, and every caller uses `Holds.iff_of_outputOn` and its two
  siblings, with no changed statement. Migration witnesses and probes:
  `tests/surface/SelectRunObservations.lean`. Tests: `just dev-build`; locally the
  fixtures of `tests/surface_select_rules_test.py`,
  `surface_select_automation_test.py`, `surface_assertion_examples_test.py`,
  `surface_claims_test.py`, `surface_proof_cost_compat_test.py`,
  `surface_s6_automation_test.py`, `surface_success_test.py`,
  `guide_view_contract_test.py` and `surface_migration_examples_test.py`.
  Follow-up: `Output.hasRows_ofResults` and `hasNoRows_ofResults` are special cases of
  `Output.returnsResult_ofResults`.
- 2026-11-07: review fixes (`refactor:`, review `20261107T030127Z-a5cf1ccf`):
  `Syntax.Statement.select_of_asQuery` moves to the model package; the plain words of
  `Holds.iff_of_outputOn` and `Empty.iff_of_outputOn` name the error, done and
  unmodeled outputs; the SELECT shape claim names the step that continues the run.
  Tests: `just dev-build`.
- 2026-11-07: execution rule (D5). `resolvedStepOutput_query_at` gives the output of a
  query step at every clock value; `resolvedStepOutput_query` is its special case.
  `Connection.SelectReady` collects the readiness premises (known counters, source rows,
  plain nested subqueries, no possible source fault, a bound window, a run without
  mismatch, overflow or fault). Under them `resolvedStepOutput_select` and
  `runScriptStep_select` give `Output.ofResults` of `possibleResults`
  (`Model/SelectExecutionRule.lean`), and `Run.send_returnsResult_select` and
  `Run.query_returnsResult_select` the iff with "every possible result has `Q`" for every
  environment (`SelectExecution.lean`). The unready rule (`resolvedStepOutput_select_unready`,
  `Run.send_unready`) is case B05. The run rule (`Query.run_single`, `Query.run_clean_iff`,
  `SelectReady.of_phases`, `Model/SelectRunRule.lean`) splits the run into the
  `fails`, `mustFail`, `mayFail` and `distinctCertain` obligations; for a calm statement
  `SelectReady.of_calm` (`Model/SelectCalmRule.lean`) discharges `mustFail` and `mayFail`,
  and keeps no overflow (`fails`) and DISTINCT certainty as premises. The general calm
  laws (`EvalContext.bound`, `Connection.queryContext_of_calm`, `Calm.faultless_nil`) move
  from `SimpleQuerySteps.lean` to that file. The model library lists
  `SelectOutputShape`, which the run observations commit left out of `lakefile.toml`, and
  the surface imports the model root instead of two model modules. Fixture:
  `tests/surface/SelectExecutionRules.lean`. Tests: `just dev-build`; locally
  `tests/surface_select_rules_test.py`, `tests/test_model_package.py`,
  `tests/surface_layers_test.py` and the source checks.
- 2026-11-07: review fix (`refactor:`, review `20261107T031515Z-b7c6a717`): the progress
  entry of the execution rule names the obligations that `SelectReady.of_calm` discharges
  and the two that stay premises.
- 2026-11-07: result, filter and projection rules (D1); A01. Every result that the model
  permits is a permutation of a sublist of the rows of the query's records, for every
  `ORDER BY` and window (`Query.exists_sublist_of_mem_possibleResults`), with its membership,
  count and length corollaries, and a permutation of all of them without `OFFSET` and
  `LIMIT` (`Query.perm_of_mem_possibleResults`, `Model/SelectWindowRules.lean`). `WHERE` keeps
  a sublist (`filtered_sublist`), all rows without a condition; a query without aggregation,
  `DISTINCT` or compound gives `Query.rowOutput` of each kept row
  (`Query.uniqueRecords_outputs_plain`), so each result row comes from a kept source row
  (`Query.mem_possibleResults_plain`), and without a window the result is a permutation of
  all of them (`Model/SelectProjectionRules.lean`). `Run.query_returnsResult_calmTable`
  (`SelectExecution.lean`) is the calm one-table form of the execution rule. A01
  (`tests/surface/SelectProjectionCases.lean`): the motivating query with generic table and
  column premises, with `db.HasCatalog invoices`, and as a `Sql.check` claim; the empty and
  populated witnesses and the nullable contrast. Tests: `just dev-build`; locally
  `tests/surface_select_rules_test.py` and `tests/surface_layers_test.py`;
  `tests/test_model_package.py` except its installed-package test, whose Nix build of the
  changed model package exceeds the local 120 s limit.
- 2026-11-07: review fixes (`refactor:`, review `20261107T033220Z-001ee122`): the result
  rules, the execution rule and their fixtures speak of the results that the model permits,
  not of every result of SQLite, and the result rules name the group row that the model fixes
  (ADR 0027 D4); `normalForm_perm` has a proof sketch. Tests: `just dev-build`.
- 2026-11-07: expression rules (D1) and A02 to A04. The value of each expression constructor
  (`Model/ExprValueRules.lean`), its possible fault (`Model/ExprFaultRules.lean`) and its calm
  condition (`Model/ExprCalmRules.lean`, with `Arguments.Calm`); the affinity of a comparison keeps
  NULL, so `x IS NOT NULL` is true exactly when `x` is not NULL, and a true ordinary comparison has
  two non-NULL operands that satisfy the operator (`Model/ComparisonTruthRules.lean`). A comparison
  whose right operand is no `TRUE` or `FALSE` keyword resolves its two operands, also for `IS` and
  `IS NOT` (`resolveOperand_compare_of_notBoolean`); a one-column read of a table with a calm
  condition is calm (`Statement.simpleColumn_calm`); `Run.returnsResult.mono` weakens the property
  of a result. A02 (`tests/surface/SelectFilterCases.lean`): `IS NOT NULL` gives non-NULL cells for a
  nullable column, with a CHECK that accepts NULL as the contrast. A03
  (`tests/surface/SelectComparisonCases.lean`): `amount > :minimum` gives the modeled comparison for
  every parameter value, with the NULL and NaN, affinity and parameter type contrasts. A04
  (`tests/surface/SelectCardinalityCases.lean`): a plain projection is a permutation of the stored
  rows' cells, so it keeps their number and duplicates, and a filter bounds the number of rows; a
  property of each row gives no number of rows and no distinct rows. A01 uses the calm corollary.
  Tests: `just dev-build`; locally `tests/surface_select_rules_test.py`,
  `tests/surface_layers_test.py` and `tests/test_model_package.py` except its installed-package
  test.

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
- `Model/QueryExamples.lean`: retain. The conformance package
  (`VerifierConformance/QueryOutputs.lean`) and the other example files import it.
- `Model/SubqueryExamples.lean`: delete. Its correlated EXISTS, IN-with-NULL and
  scalar-subquery examples are the contrasts of A18 and A19, which replace them.
- `Model/QueryWindowExamples.lean`: delete the examples of the queries `windowed` and
  `empty` (parameter LIMIT/OFFSET results and the mismatch error); A15 replaces them.
  Retain the `windowInteger` conversion examples (integer, real, text, blob and NULL
  values of a window parameter): no acceptance case covers that conversion table.
- `Model/PossibleResultsExamples.lean`: delete the `possible` examples (window ties,
  DISTINCT and LIMIT over the guide's tables); A12 and A14 replace them. Retain the two
  `Resolved.normalForm` examples (NaN against NULL, and real 1.0 against integer 1):
  no case covers the order of output normalization.
- `Model/InSubqueryExamples.lean`: retain. Its NOT IN against NOT EXISTS examples
  (NULL, empty subquery and collation) protect the equivalence of `NotInQuery.lean`
  (ADR 0026 D4), which no ADR 27 case covers; A19 covers one IN observation, not the
  equivalence.
