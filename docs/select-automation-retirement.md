# SELECT proof automation: retirement inventory

Date: 2026-10-29. Status: ACCEPTED with ADR 0027 (owner, 2026-11-07); owner decisions of 2026-10-29 applied;
reconciled to main `84c0d779` on 2026-11-06.
Audience: designers and reviewers. Governing proposal:
[ADR 0027](adr-0027-compositional-select-proofs.md), section "Scope and
supersession". Completion rule: [acceptance contract](select-automation-acceptance.md),
section "Meaning of completion".

This inventory names the code that the phase rules of ADR 0027 replace. The
project has no users: replaced code is deleted, not kept behind an alias. Line
counts are from main `84c0d779` and are for orientation only.

## How to read the inventory

- **Required**: delete when the phase rules of the named family exist and the
  family's acceptance cases pass. The implementer migrates every caller first.
- **Candidate**: the implementer decides at assignment. A candidate that stays
  is recorded in the status file with the reason: a consumer that the phase
  rules cannot serve, a premise boundary that no acceptance case protects, or
  a law that is general and not tied to one query form.
- **Retained**: not in scope. Listed so that the boundary is explicit.

## Surface query forms (ADR 0017 S4)

Each form file is about one syntactic shape over every database and holds one
or more of: a `Script.outputOn_<form>` complete-output equation (ADR 0026 D1),
`Holds`, `Empty` or `Fails` claim theorems, or schema-hint functions.
`CountQuery`, `AggregateQuery`, `ColumnQuery`, `ExistsQuery` and
`NotExistsQuery` hold only output equations; `SelectOneFrom`, `SelectNoFrom`,
`DuplicateKeyQuery` and `FilteredDuplicateKeyQuery` hold both; `UniqueLookupQuery`
holds one `Holds` claim; `ExistsMayFail` and `SelectOneMayFail` hold the
`Script.not_claims_*` negative claims; `QueryCases` holds the `*.iff_step`
case splits and the prepare-error output equation; `ScalarNoFrom` holds the three quiet-statement laws of a
scalar query without `FROM`. The shape is a whole-query lemma,
which D3 says automation must not need. The equations and claims become the
"required contrast" column of the acceptance matrix. Line counts are the
current ones on main `84c0d779`; the fifteen files total 1,328 lines.

| File under `packages/belay/Belay/Sqlite/` | Acceptance cover | Status |
| --- | --- | --- |
| `CountQuery.lean` (74) | A08 | Deleted: `ClaimsCount.lean`, `CustomerInsertQueries.lean`, `AccountSignupQueries.lean` and `ExpansionCountQueries.lean` prove their claims for every database through the subquery run rule, the ungrouped rule `Resolved.records_ungrouped` and `whereOne_claims`, with the support of `SelectCountWhereSupport.lean` |
| `AggregateQuery.lean` (86) | A08, A09 | Deleted: `SelectCountCases.lean` and `SelectNullAggregateCases.lean` cover A08 and A09 through the aggregate rules |
| `ColumnQuery.lean` (95) | A19 | Deleted: `ClaimsIn.lean` proves its claims for every database through the subquery run rule, `Resolved.Query.results_plain_unordered` and `whereOne_claims`, with the support of `SelectColumnWhereSupport.lean` |
| `SelectOneFrom.lean` (136) | A01, A02 | Deleted: `SelectExistenceCases.lean` proves the existence and emptiness claims through `Resolved.Query.forall_possibleResults_ne_nil_plain` and `Resolved.Query.forall_possibleResults_eq_nil_plain` |
| `SelectNoFrom.lean` (91) | A20 | Deleted: `SelectSourceCases.lean` proves `SELECT 1 + 2` for every database, and `SelectFunctionFaultCases.lean` proves that `WHERE 0` gives no row for every database |
| `ExistsQuery.lean`, `NotExistsQuery.lean` (123) | A18 | Deleted: `ClaimsExists.lean` and `CustomerInsertQueries.lean` prove their claims for every database through `Run.query_returnsResult_faultless` and the subquery run rule, with the support of `SelectOneWhereSupport.lean` |
| `DuplicateKeyQuery.lean`, `FilteredDuplicateKeyQuery.lean` (263) | A07, A10 | Deleted: `ClaimsDuplicateKeys.lean`, `SuccessUniqueEmail.lean` and `GlobalSignupInvariant.lean` prove their claims for every database through the subquery run rule, `Resolved.Query.results_unordered`, `Resolved.records_aggregate`, `Resolved.queryGroups_grouped` and `whereOne_claims`, with the support of `SelectDuplicateKeySupport.lean` |
| `UniqueLookupQuery.lean` (57) | A05 | Deleted: `ClaimsUniqueLookup.lean` proves the bound of a unique lookup for every database through `whereCount_claims` and `Table.KeysUnique.countMatching_le_one` |
| `ScalarNoFrom.lean` (83) | A20, B01, B05 | Deleted: `SelectFunctionFaultCases.lean` proves its three claims for every database and environment through `SelectReady.of_phases` and `Run.send_mustFail`, which take a quiet statement and so keep fallible functions |
| `ExistsMayFail.lean`, `SelectOneMayFail.lean` (113) | B05 | Deleted: `ClaimsMayFail.lean` proves their claims for every database and environment through `Run.send_unready` |
| `QueryCases.lean` (132) | B01, B11 | Deleted: `SelectOutcomeCases.lean` proves B01 and B11 for every database and environment through `Run.query_prepareError` and `Sql.check_stopped`; `SelectPrepareErrorCases.lean` adds a body error for every database through `resolveStatement_select_body_prepareError`; `ClaimsMayFail.lean` keeps the unmodeled claims through `Run.send_unready`; `SuccessBalanceSuccess.lean` uses `Run.query_prepareError` |
| `SampleQueryHints.lean` (66) | none | Retained (owner, 2026-11-07): the traversal of SQL clauses that gives candidate schemas to the sample checker (`SampleScriptHints`, `CheckClaim`, `CheckSamples`). It is not tied to one query form, and the proof hints of D6 do not replace it |
| `TableInfoQuery.lean` (66) | A20 (pragma rows) | Deleted: `ClaimsTableInfo.lean` uses the pragma source rule `Resolved.Query.source_pragma` |
| `NotInQuery.lean` (150) | ADR 0026 D4 consumer | Retained: an `EquivAt` law, not a claim form |
| `Queries.lean`, `QueryLaws.lean`, `QuerySuccess.lean`, `QueryBridge.lean` (378) | D2 | Retained: the claim layer. `Holds`, `Empty` and `Fails` are redefined as abbreviations, see ADR 0027 D2 |

## ADR 0026 D1 owners

[PR 297](https://github.com/vihren-dev/belay/pull/297) completed
ADR 0026 D1 on main. ADR 0027 supersedes D1: a phase decomposition replaces a
per-family characterization. The owners are named as they exist on main.

| Owner on main | Status |
| --- | --- |
| `resolvedStepOutput_selectOne` in `SelectOneOutput.lean` (35) and the per-family output files below that apply it (count, scalar column, EXISTS, NOT EXISTS, duplicate key) | Deleted: after the retirement of the surface forms no caller remained |
| `AggregateQueryOutput.lean` | Deleted, with `AggregateQuery.lean` (see the model per-family output laws) |
| `QueryOutputFacts.lean` (98): `Query.described`, `resolvedStepOutput_query`, `resolvedStepOutput_query_source`, `Connection.runOn_of_found`, `normalForm_eq_nil` | Retained: the execution bridge of D5 uses them |
| `QueryStatementOutput.lean`: `Fault.ne_must_iff_none`, `resolvedStepOutput_query_hasRows`, `_hasNoRows`, `_isError` | Retained: generic observation laws |
| The resolver-only transports (`*Resolution.lean`) | Retained: see "Resolution-shape laws" |
| The surface `Script.outputOn_<form>` equations in the files of the table above | Deleted, with the surface forms above. The generic `Script.outputOn_query`, `outputOn_eq_step`, `outputOn_isQuery` and `outputOn_eq_outputIn` stay |

## Model per-family output laws

| File under `packages/belay-sqlite-model/Belay/Sqlite/Model/` | Lines | Status |
| --- | --- | --- |
| `SelectOneRowsOutput`, `SelectOneSubqueryOutput`, `SelectOneOutput` | 277 | Deleted: after the retirement of the surface forms no caller remained |
| `SimpleTableRowsOutput`, `SimpleSubqueryRowsOutput` | 164 | Deleted: the calm rule `resolvedStepOutput_calm_unordered` in `SelectCalmRule` gives the exact output of a calm query without order or window, and `resolvedStepOutput_select_unordered` in `SelectExecutionRule` that of a ready one |
| `DuplicateKeyOutput` | 109 | Deleted, with `DuplicateKeyQuery.lean` and `FilteredDuplicateKeyQuery.lean`; the fixture `SelectDuplicateKeySupport.lean` proves the calmness of the statement and the run of the subquery |
| `ScalarSubqueryOutput` | 127 | Deleted, with `ColumnQuery.lean`; `Resolved.Statement.Calm.selectOne_scalar` became the general `Resolved.Statement.Calm.selectOne_subquery` in `SelectOneSubqueryContext`, and `Connection.queryContext_tableSubquery_zero`, which only this file used, is deleted |
| `CountSubqueryOutput` | 116 | Deleted, with `CountQuery.lean`; `Resolved.Statement.Calm.selectOne_count` moved to `SelectOneSubqueryContext`, and the count query `Resolved.Query.countOf` with `Resolved.SubqueryRun.count` to `CountOf` |
| `AggregateQueryOutput` | 62 | Deleted, with `AggregateQuery.lean` |
| `SimpleTableOutput` | 67 | Deleted, with `SelectOneFrom.lean` |
| `ExistsSubqueryOutput`, `NotExistsSubqueryOutput` | 154 | Deleted, with `ExistsQuery.lean` and `NotExistsQuery.lean`; the subquery context laws and `Resolved.Statement.Calm.selectOne_subquery` moved to `SelectOneSubqueryContext` |
| `QueryMayFailOutput`, `SubqueryMayFailOutput` | 204 | Deleted, with `SelectOneMayFail.lean` and `ExistsMayFail.lean`; `Resolved.Statement.Quiet.selectOne` moved to `SelectOneResolution` and `Resolved.Statement.Quiet.selectOne_subquery` to `SelectOneSubqueryContext` |
| `SelectNoFromOutput` | 68 | Deleted, with `SelectNoFrom.lean`; a certainly failing call uses `resolvedStepOutput_select_mustFail` in `SelectFailureRule` |
| `TableInfoOutput` | 68 | Deleted, with `TableInfoQuery.lean`; `Resolved.Statement.Calm.selectOne_pragma` moved to `SelectSourceRules` |
| `QueryStatementOutput`, `QueryStepOutput`, `QueryOutputOn`, `QueryOutputRows`, `QueryOutputCases`, `Output`, `StatementOutput`, `OneTableStatementOutput`, `NonQueryOutput`, `PrepareErrorOutput`, `PossibleOutput` | — | Retained: generic observation and execution laws |
| `TwoStateNotExistsExceptOutput` | 86 | Retained: two-state observation |

## Model per-family laws and steps

| File | Lines | Status |
| --- | --- | --- |
| `CountQueryLaws` | 118 | Deleted: the ungrouped rule `Resolved.records_ungrouped` replaces its `Query.Count` laws |
| `AggregateQueryLaws` | 127 | Deleted: the query `Resolved.Query.aggregateOf` moved to `AggregateSelectResolution`, which gives it. Its result and overflow laws became the general rules `Query.possibleResults_ungrouped` and `Query.fails_ungrouped` of an aggregate query without `GROUP BY` in `UngroupedQueryRules`; the fixtures `SelectSumCases.lean` and `SuccessBalanceSuccess.lean` use them. `countOf_eq_aggregateOf` had no caller |
| `NoFromQuerySteps` | 104 | Deleted: the query `Resolved.Query.selectOneWhere` and its laws moved to `PlainQueryRules`; the fixture `SuccessBalanceObservation.lean` reads the guard through `resolvedStepOutput_select_unordered` |
| `DuplicateKeyQuery` | 176 | Reduced to 33 lines: it keeps the definitions `Resolved.Query.duplicateKeys`, which `DuplicateKeyResolution` gives, and `Resolved.keptRows`. Its laws are deleted; the fixture `SelectDuplicateKeySupport.lean` keeps their generality, expression keys under `key.Calm` (ADR 0030 D7) |
| `DuplicateKeyGroupTerm` | 113 | Retained: the resolution of the grouping term (`GroupTermResolves`), which the premises of the support use |
| `SimpleQueryFaults` | 95 | Deleted: `Resolved.Statement.Quiet.selectNoFrom` moves to `SelectSourceRules`, and no caller of its other laws remained |
| `SimpleQueryLaws`, `SimpleResultsLaws`, `SimpleQuerySteps`, `SimpleSubqueryRun` | 369 | Deleted, with the predicate `Query.Simple`. The query `Resolved.Query.simple` moved to `PlainQueryRules`. `Simple.results_eq` and `results_length` became `Query.results_plain_unordered` in `SelectSubqueryRules`, `Simple.run_of_faultless` became `Query.run_of_faultless` in `QueryPlainLaws`, `Simple.possibleResults_eq` became `Query.possibleResults_unordered`, and `resolvedStepOutput_simple_not_isError_of_faultless` became `resolvedStepOutput_not_isError_of_faultless` in `SelectCalmRule`, each with only the field premises that its proof reads |
| `SimpleQueryAppend`, `SimpleTableCalm` | 145 | Retained: read-certificate laws of ADR 0017 (S6) over the query `Resolved.Query.simple`, with no `Query.Simple` premise. `CertifiedQueryOutputs` uses them |
| `InSubqueryColumnLaw`, `InSubqueryEqualityLink`, `InSubqueryEvaluate`, `InSubqueryFilterLaw`, `InSubqueryQueryInLaw`, `InSubqueryQueryLaw`, `InSubqueryQueryRowidAlias`, `InSubqueryRowidAlias` | 863 | Retained (decided at assignment, 2026-11-07): `NotInQuery.lean` (ADR 0026 D4) uses `resolvedStepOutput_in_eq_exists_of_rowidAlias` and `resolvedStepOutput_notIn_eq_notExists_of_rowidAlias`, whose proofs use every other declaration of the chain except three. Those three had no caller and are deleted: `correlatedEquality_of_guarded_compare`, `Expr.evaluate_notIn_eq_notExists_of_rowidAlias` and `Expr.evaluate_in_truthy_eq_exists_of_rowidAlias` |
| `SelectStepKeeps` | 133 | Retained: ADR 0025 preservation |

## Resolution-shape laws

Each file states that one syntactic shape resolves to one `Query` value for a
symbolic catalog. No general replacement exists: the ADR 0026 D3 certificate
takes successful resolution as a premise and gives state equality, schema
linkage and validity, not the resolution equation. These laws stay. A file is
deleted only when every consumer is a retired form and no acceptance case
needs its equation; the status file records each such deletion.

| File | Lines | Status |
| --- | --- | --- |
| `CountSelectResolution`, `CountStatementResolution`, `AggregateSelectResolution`, `ExistsStatementResolution`, `InSubqueryStatementResolution`, `ScalarSubqueryResolution`, `SelectNoFromResolution`, `SelectOneResolution`, `DuplicateKeyResolution`, `SimpleSelectResolution`, `SimpleSourceResolution`, `SimpleStatementResolution`, `SubquerySelectResolution`, `FromSubquerySelectResolution`, `FromSubqueryStatementResolution`, `FromSourceResolution` | 1,678 | Retained, unless every consumer is retired |
| `BackfillStatementResolution` | 103 | Retained: migration |

## Examples and fixtures

| Location | Status |
| --- | --- |
| `tests/surface/ClaimsQueryCases.lean` | Deleted: the B fixtures take its place. Its nested prepare errors and the contrast of a known column move to `SelectPrepareErrorCases.lean` (B11), the clock read to `SelectOutcomeCases.lean` (B01), the `LIMIT` alternatives to `SelectOutcomeCases.lean` (B02), the `LIMIT NULL` mismatch to `SelectParameterWindowCases.lean` (A15) and the malformed `json_each` source to `SelectSourceCases.lean` (A20) |
| `tests/surface/Queries/Tests/ClaimsExists.lean`, `ClaimsMayFail.lean` | Retained: they keep the claims of the deleted EXISTS and may-fail forms, now proved through the phase rules. The acceptance fixtures are `SelectExistsCases.lean` for A18, whose subquery is correlated, and `SelectExecutionRules.lean` for B05 |
| `tests/surface/Queries/Tests/ClaimsCount.lean`, `ClaimsUniqueLookup.lean`, `ClaimsIn.lean`, `ClaimsDuplicateKeys.lean` | Retained: they keep the claims of the deleted count, unique-lookup, column and duplicate-key forms, now proved through the phase rules. The acceptance fixtures are `SelectCountCases.lean` for A08, `SelectJoinCases.lean` for A05, `SelectInCases.lean` and `SelectScalarCases.lean` for A19, and `SelectGroupCases.lean` and `SelectHavingCases.lean` for A07 and A10 |
| `tests/surface/ClaimsSelectOne.lean`, `ClaimsSum.lean`, `ClaimsAggregateLaws.lean` | Deleted, with `SelectOneFrom.lean` and `AggregateQuery.lean`: `SelectExistenceCases.lean`, `SelectCountCases.lean` and `SelectNullAggregateCases.lean` take their place |
| `tests/surface/ClaimsNoFrom.lean`, `ClaimsScalarNoFrom.lean` | Deleted, with `SelectNoFrom.lean` and `ScalarNoFrom.lean`: `SelectSourceCases.lean` and `SelectFunctionFaultCases.lean` prove their claims and instances |
| `tests/surface/ClaimsTableInfo*.lean`, `ClaimsView*.lean`, `ClaimsDerived.lean`, `ClaimsCommonTables.lean`, `ClaimsExpressionLaws.lean` | Retained unless their subject is a retired form; reconcile at assignment |
| Model `QueryExamples`, `SubqueryExamples`, `QueryWindowExamples`, `PossibleResultsExamples`, `InSubqueryExamples` | A necessity example that an acceptance contrast repeats is deleted; one that protects a boundary no case covers stays. `SubqueryExamples` stays: no acceptance case checks its depth-two correlation or its fault contrasts of a scalar subquery and of `IN` over a window. `PossibleResultsExamples` stays: no acceptance case checks the exact alternatives of `LIMIT` without `ORDER BY`, of a window across tie groups, or of `DISTINCT` and `GROUP BY` with `LIMIT`. `QueryExamples` and `InSubqueryExamples` stay. `QueryWindowExamples` keeps its `windowInteger` examples; its query examples are deleted, and their window boundaries (a negative `LIMIT` or `OFFSET`, a value that is not given, `WHERE 0` with `OFFSET NULL`) are contrasts of A15 in `SelectParameterWindowCases.lean` |
| `tests/surface/Queries/Evaluation/ClaimsGroupValues.lean`, `ClaimsExpressionGrouping.lean`, `ClaimsConditionalCreation.lean` (ADR 0030) | Retained: they check model semantics through execution and use no per-form law |
| `tests/surface/SelectAutomation*.lean` | Retained through the last slice that changes their contracts, then deleted when the A and B fixtures cover their claims (ADR 0025 D4 test lifetime) |

## Not replaced

- The core evaluator and its generic laws: `QueryEval`, `QueryResults`,
  `QueryRun`, `QueryFunctions`, `QueryJoins`, `QueryJoinLaws`, `QueryWindow`,
  `QueryLaws`, `QueryPlainLaws`, `Subqueries`, `CompoundRows`, `CompoundRun`, and
  `GroupRow` with the grouping resolution of ADR 0030 (`GroupAssociation`).
  The phase rules are stated over these definitions.
- `PossibleResults*`: the rules quantify over every permitted result.
- ADR 0026 D2 source agreement, D4 execution profiles, D5 expression
  congruence and D3 resolver certificates.
- Two-state, migration and read-certificate laws: `DerivedColumn*`,
  `ReadCertificate*`, `MigrationQueryFrames`, `TwoStateAssertions`.
- `Sql.check`, `sql_run`, `sql_auto`, `AutoSearch` and the `mvcgen` integration.

## Measurement

The net reduction is not established. The physical counts above are the gross
deletion opportunity: by `scc`, the fifteen surface files hold 905 maintained
code lines and the required model files 1,648, together 2,553, before retained
laws move. Measure the first completed family, with its retained-law moves, the
tactic code, the migrated clients and the tests, and use that result to decide
the remaining scope.

Record in the status file, once at completion: lines deleted by this inventory,
lines added by the rule library and tactic, and the net change in maintained
Lean lines, against the [Lean simplification goal](lean-simplification-goal.md).
Before/after counts are one-time acceptance work, not a CI check.
