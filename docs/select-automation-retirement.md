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
case splits and the prepare-error output equation; `SampleQueryHints` holds
the hint functions; `ScalarNoFrom` holds the three quiet-statement laws of a
scalar query without `FROM`. The shape is a whole-query lemma,
which D3 says automation must not need. The equations and claims become the
"required contrast" column of the acceptance matrix. Line counts are the
current ones on main `84c0d779`; the fifteen files total 1,328 lines.

| File under `packages/belay/Belay/Sqlite/` | Acceptance cover | Status |
| --- | --- | --- |
| `CountQuery.lean` | A08 | Required |
| `AggregateQuery.lean` | A08, A09 | Required |
| `ColumnQuery.lean` | A19 | Required |
| `SelectOneFrom.lean` | A01, A02 | Required |
| `SelectNoFrom.lean` (91) | A20 | Deleted: `SelectSourceCases.lean` proves `SELECT 1 + 2` for every database, and `SelectFunctionFaultCases.lean` proves that `WHERE 0` gives no row for every database |
| `ExistsQuery.lean`, `NotExistsQuery.lean` (123) | A18 | Deleted: `ClaimsExists.lean` and `CustomerInsertQueries.lean` prove their claims for every database through `Run.query_returnsResult_faultless` and the subquery run rule, with the support of `SelectOneWhereSupport.lean` |
| `DuplicateKeyQuery.lean`, `FilteredDuplicateKeyQuery.lean` | A07, A10 | Required |
| `UniqueLookupQuery.lean` | A05 | Required |
| `ScalarNoFrom.lean` (83) | A20, B01, B05 | Deleted: `SelectFunctionFaultCases.lean` proves its three claims for every database and environment through `SelectReady.of_phases` and `Run.send_mustFail`, which take a quiet statement and so keep fallible functions |
| `ExistsMayFail.lean`, `SelectOneMayFail.lean` (113) | B05 | Deleted: `ClaimsMayFail.lean` proves their claims for every database and environment through `Run.send_unready` |
| `QueryCases.lean` | B01, B11 | Required |
| `SampleQueryHints.lean` | D6 hints | Required |
| `TableInfoQuery.lean` (66) | A20 (pragma rows) | Deleted: `ClaimsTableInfo.lean` uses the pragma source rule `Resolved.Query.source_pragma` |
| `NotInQuery.lean` (150) | ADR 0026 D4 consumer | Retained: an `EquivAt` law, not a claim form |
| `Queries.lean`, `QueryLaws.lean`, `QuerySuccess.lean`, `QueryBridge.lean` (378) | D2 | Retained: the claim layer. `Holds`, `Empty` and `Fails` are redefined as abbreviations, see ADR 0027 D2 |

## ADR 0026 D1 owners

[PR 297](https://github.com/vihren-dev/belay/pull/297) completed
ADR 0026 D1 on main. ADR 0027 supersedes D1: a phase decomposition replaces a
per-family characterization. The owners are named as they exist on main.

| Owner on main | Status |
| --- | --- |
| `resolvedStepOutput_selectOne` in `SelectOneOutput.lean` (35) and the per-family output files below that apply it (count, scalar column, EXISTS, NOT EXISTS, duplicate key) | Required |
| `AggregateQueryOutput.lean` | Required, after the `aggregate` phase rule exists |
| `QueryOutputFacts.lean` (98): `Query.described`, `resolvedStepOutput_query`, `resolvedStepOutput_query_source`, `Connection.runOn_of_found`, `normalForm_eq_nil` | Retained: the execution bridge of D5 uses them |
| `QueryStatementOutput.lean`: `Fault.ne_must_iff_none`, `resolvedStepOutput_query_hasRows`, `_hasNoRows`, `_isError` | Retained: generic observation laws |
| The resolver-only transports (`*Resolution.lean`) | Retained: see "Resolution-shape laws" |
| The surface `Script.outputOn_<form>` equations in the files of the table above | Required, with the surface forms above |

## Model per-family output laws

| File under `packages/belay-sqlite-model/Belay/Sqlite/Model/` | Lines | Status |
| --- | --- | --- |
| `CountSubqueryOutput`, `AggregateQueryOutput`, `ScalarSubqueryOutput`, `SelectOneRowsOutput`, `SelectOneSubqueryOutput`, `DuplicateKeyOutput`, `SimpleTableOutput`, `SimpleTableRowsOutput`, `SimpleSubqueryRowsOutput`, `SelectOneOutput` | 921 | Required |
| `ExistsSubqueryOutput`, `NotExistsSubqueryOutput` | 154 | Deleted, with `ExistsQuery.lean` and `NotExistsQuery.lean`; the subquery context laws and `Resolved.Statement.Calm.selectOne_subquery` moved to `SelectOneSubqueryContext` |
| `QueryMayFailOutput`, `SubqueryMayFailOutput` | 204 | Deleted, with `SelectOneMayFail.lean` and `ExistsMayFail.lean`; `Resolved.Statement.Quiet.selectOne` moved to `SelectOneResolution` and `Resolved.Statement.Quiet.selectOne_subquery` to `SelectOneSubqueryContext` |
| `SelectNoFromOutput` | 68 | Deleted, with `SelectNoFrom.lean`; a certainly failing call uses `resolvedStepOutput_select_mustFail` in `SelectFailureRule` |
| `TableInfoOutput` | 68 | Deleted, with `TableInfoQuery.lean`; `Resolved.Statement.Calm.selectOne_pragma` moved to `SelectSourceRules` |
| `QueryStatementOutput`, `QueryStepOutput`, `QueryOutputOn`, `QueryOutputRows`, `QueryOutputCases`, `Output`, `StatementOutput`, `OneTableStatementOutput`, `NonQueryOutput`, `PrepareErrorOutput`, `PossibleOutput` | — | Retained: generic observation and execution laws |
| `TwoStateNotExistsExceptOutput` | 86 | Retained: two-state observation |

## Model per-family laws and steps

| File | Lines | Status |
| --- | --- | --- |
| `CountQueryLaws`, `AggregateQueryLaws`, `DuplicateKeyQuery`, `DuplicateKeyGroupTerm`, `NoFromQuerySteps` | 638 | Required: their content becomes the `group`, `aggregate`, `having` and `source` rules. A general law that a file holds moves to the rule library before the file is deleted. The duplicate-key laws cover expression keys under `key.Calm` (ADR 0030 D7); the group rule keeps that generality |
| `SimpleQueryLaws`, `SimpleResultsLaws`, `SimpleQueryAppend`, `SimpleQueryFaults`, `SimpleQuerySteps`, `SimpleSubqueryRun`, `SimpleTableCalm` | 609 | Required: `Query.Simple` is a phase decomposition of one shape. `Simple.results_eq` becomes the `project` rule, `results_length` the `filter` cardinality rule, and the predicate is deleted |
| `InSubqueryColumnLaw`, `InSubqueryEqualityLink`, `InSubqueryEvaluate`, `InSubqueryFilterLaw`, `InSubqueryQueryInLaw`, `InSubqueryQueryLaw`, `InSubqueryQueryRowidAlias`, `InSubqueryRowidAlias` | 863 | Candidate: `NotInQuery.lean` and the ADR 0026 D4 equivalences consume part of them. Keep what those consumers need; the rest becomes the `subquery` rule |
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
| `tests/surface/Claims{Count,Sum,In,SelectOne,DuplicateKeys,UniqueLookup,QueryCases,AggregateLaws}.lean` | Required: replaced by the A and B fixtures. A negative case that a fixture uniquely protects moves to the "required contrast" of its acceptance case before the fixture is deleted |
| `tests/surface/ClaimsExists.lean`, `ClaimsMayFail.lean` | Retained: their claims are proved through the phase rules, so they are the A18 and B05 acceptance fixtures |
| `tests/surface/ClaimsNoFrom.lean`, `ClaimsScalarNoFrom.lean` | Deleted, with `SelectNoFrom.lean` and `ScalarNoFrom.lean`: `SelectSourceCases.lean` and `SelectFunctionFaultCases.lean` prove their claims and instances |
| `tests/surface/ClaimsTableInfo*.lean`, `ClaimsView*.lean`, `ClaimsDerived.lean`, `ClaimsCommonTables.lean`, `ClaimsExpressionLaws.lean` | Retained unless their subject is a retired form; reconcile at assignment |
| Model `QueryExamples`, `SubqueryExamples`, `QueryWindowExamples`, `PossibleResultsExamples`, `InSubqueryExamples` | A necessity example that an acceptance contrast repeats is deleted; one that protects a boundary no case covers stays. `SubqueryExamples` stays: no acceptance case checks its depth-two correlation or its fault contrasts of a scalar subquery and of `IN` over a window. `PossibleResultsExamples` stays: no acceptance case checks the exact alternatives of `LIMIT` without `ORDER BY`, of a window across tie groups, or of `DISTINCT` and `GROUP BY` with `LIMIT`. `QueryExamples` and `InSubqueryExamples` stay. `QueryWindowExamples` keeps its `windowInteger` examples; its query examples go when `ClaimsQueryCases.lean` is deleted |
| `tests/surface/ClaimsGroupValues.lean`, `ClaimsExpressionGrouping.lean`, `ClaimsConditionalCreation.lean` (ADR 0030) | Retained: they check model semantics through execution and use no per-form law |
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
