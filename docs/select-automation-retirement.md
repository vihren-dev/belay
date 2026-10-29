# SELECT proof automation: retirement inventory

Date: 2026-10-29. Status: DRAFT; owner decisions of 2026-10-29 applied.
Audience: designers and reviewers. Governing proposal:
[ADR 0027](adr-0027-compositional-select-proofs.md), section "Scope and
supersession". Completion rule: [acceptance contract](select-automation-acceptance.md),
section "Meaning of completion".

This inventory names the code that the phase rules of ADR 0027 replace. The
project has no users: replaced code is deleted, not kept behind an alias. Line
counts are from the baseline `3e2212ed` and are for orientation only.

## How to read the inventory

- **Required**: delete when the phase rules of the named family exist and the
  family's acceptance cases pass. The implementer migrates every caller first.
- **Candidate**: the implementer decides at assignment. A candidate that stays
  is recorded in the status file with the reason: a consumer that the phase
  rules cannot serve, a premise boundary that no acceptance case protects, or
  a law that is general and not tied to one query form.
- **Retained**: not in scope. Listed so that the boundary is explicit.

The baseline predates [PR 297](https://github.com/vihren-dev/sqlite-verifier/pull/297),
which completed ADR 0026 D1. Reconcile at assignment: the names in "ADR 0026
D1 owners" below come from that pull request, and a file that PR 297 deleted or
renamed is reconciled to its replacement, not restored.

## Surface query forms (ADR 0017 S4)

Each file proves `Holds`, `Empty` and `Fails` for one syntactic shape over every
database. The shape is a whole-query lemma, which D3 says automation must not
need. Their claims become the "required contrast" column of the acceptance
matrix.

| File under `packages/belay/Belay/Sqlite/` | Lines | Acceptance cover | Status |
| --- | --- | --- | --- |
| `CountQuery.lean` | 135 | A08 | Required |
| `AggregateQuery.lean` | 159 | A08, A09 | Required |
| `ColumnQuery.lean` | 172 | A19 | Required |
| `SelectOneFrom.lean` | 136 | A01, A02 | Required |
| `SelectNoFrom.lean` | 94 | A20 | Required |
| `ExistsQuery.lean`, `NotExistsQuery.lean` | 227 | A18 | Required |
| `DuplicateKeyQuery.lean`, `FilteredDuplicateKeyQuery.lean`, `FilteredDuplicateKeyEmpty.lean` | 412 | A07, A10 | Required |
| `UniqueLookupQuery.lean` | 56 | A05 | Required |
| `ExistsMayFail.lean`, `SelectOneMayFail.lean` | 113 | B05 | Required |
| `QueryCases.lean` | 135 | B01, B11 | Required |
| `SampleQueryHints.lean` | 66 | D6 hints | Required |
| `TableInfoQuery.lean` | 117 | A20 (pragma rows) | Candidate: the metadata fixtures `ClaimsTableInfo*.lean` may need it |
| `NotInQuery.lean` | 150 | ADR 0026 D4 consumer | Retained: an `EquivAt` law, not a claim form |
| `Queries.lean`, `QueryLaws.lean`, `QuerySuccess.lean`, `QueryBridge.lean` | 375 | D2 | Retained: the claim layer. `Holds`, `Empty` and `Fails` are redefined as abbreviations, see ADR 0027 D2 |

## ADR 0026 D1 owners

The ADR 0026 D1 implementation in PR 297 replaces 45 endpoints with seven model
and eight surface complete-output facts. That implementation and the owner names
below are not in this branch yet. Here, `Query.described` and
`resolvedStepOutput_query` still live in `QueryStatementOutput.lean`.
ADR 0027 supersedes D1 after integration: a phase decomposition replaces a
per-family characterization. Reconcile the exact names at assignment from
PR 297's `plans/20261028-query-output-facts.status.md`.

| Owner (PR 297) | Status |
| --- | --- |
| The SELECT-1 output fact in `SelectOneOutput` and its five consumer families (count, scalar column, EXISTS, NOT EXISTS, duplicate key) | Required |
| The aggregate output fact | Required, after the `aggregate` phase rule exists |
| The general source-output equation and the moved context and source definitions in `QueryOutputFacts` (`Query.described`, `resolvedStepOutput_query`, `resolvedStepOutput_query_source`) | Retained: the execution bridge of D5 uses them |
| The eight resolver-only transports | Retained: see "Resolution-shape laws" |
| The eight surface complete-output equations | Required, with the surface forms above |

## Model per-family output laws

| File under `packages/belay-sqlite-model/Belay/Sqlite/Model/` | Lines | Status |
| --- | --- | --- |
| `CountSubqueryOutput`, `AggregateQueryOutput`, `ExistsSubqueryOutput`, `NotExistsSubqueryOutput`, `ScalarSubqueryOutput`, `SelectOneRowsOutput`, `SelectOneSubqueryOutput`, `SelectNoFromOutput`, `DuplicateKeyOutput`, `SimpleTableOutput`, `SimpleTableRowsOutput`, `SimpleSubqueryRowsOutput`, `QueryMayFailOutput`, `SubqueryMayFailOutput` | 1,540 | Required |
| `TableInfoOutput` | 97 | Candidate, with `TableInfoQuery.lean` |
| `QueryStatementOutput`, `QueryStepOutput`, `QueryOutputOn`, `QueryOutputRows`, `QueryOutputCases`, `Output`, `StatementOutput`, `OneTableStatementOutput`, `NonQueryOutput`, `PrepareErrorOutput`, `PossibleOutput` | — | Retained: generic observation and execution laws |
| `TwoStateNotExistsExceptOutput` | 86 | Retained: two-state observation |

## Model per-family laws and steps

| File | Lines | Status |
| --- | --- | --- |
| `CountQueryLaws`, `AggregateQueryLaws`, `DuplicateKeyQuery`, `DuplicateKeyGroupTerm`, `NoFromQuerySteps` | 608 | Required: their content becomes the `group`, `aggregate`, `having` and `source` rules. A general law that a file holds moves to the rule library before the file is deleted |
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
| `CountSelectResolution`, `CountStatementResolution`, `AggregateSelectResolution`, `ExistsStatementResolution`, `InSubqueryStatementResolution`, `ScalarSubqueryResolution`, `SelectNoFromResolution`, `SelectOneResolution`, `DuplicateKeyResolution`, `SimpleSelectResolution`, `SimpleSourceResolution`, `SimpleStatementResolution`, `SubquerySelectResolution`, `FromSubquerySelectResolution`, `FromSubqueryStatementResolution`, `FromSourceResolution` | 1,725 | Retained, unless every consumer is retired |
| `BackfillStatementResolution` | 103 | Retained: migration |

## Examples and fixtures

| Location | Status |
| --- | --- |
| `tests/surface/Claims{Count,Sum,Exists,In,SelectOne,NoFrom,ScalarNoFrom,DuplicateKeys,UniqueLookup,QueryCases,MayFail,AggregateLaws}.lean` | Required: replaced by the A and B fixtures. A negative case that a fixture uniquely protects moves to the "required contrast" of its acceptance case before the fixture is deleted |
| `tests/surface/ClaimsTableInfo*.lean`, `ClaimsView*.lean`, `ClaimsDerived.lean`, `ClaimsCommonTables.lean`, `ClaimsExpressionLaws.lean` | Retained unless their subject is a retired form; reconcile at assignment |
| Model `QueryExamples`, `SubqueryExamples`, `QueryWindowExamples`, `PossibleResultsExamples`, `InSubqueryExamples` | Candidate: a necessity example that an acceptance contrast repeats is deleted; one that protects a boundary no case covers stays |
| `tests/surface/SelectAutomation*.lean` | Retained through the last slice that changes their contracts, then deleted when the A and B fixtures cover their claims (ADR 0025 D4 test lifetime) |

## Not replaced

- The core evaluator and its generic laws: `QueryEval`, `QueryResults`,
  `QueryRun`, `QueryFunctions`, `QueryJoins`, `QueryJoinLaws`, `QueryWindow`,
  `QueryLaws`, `QueryPlainLaws`, `Subqueries`, `CompoundRows`, `CompoundRun`.
  The phase rules are stated over these definitions.
- `PossibleResults*`: the rules quantify over every permitted result.
- ADR 0026 D2 source agreement, D4 execution profiles, D5 expression
  congruence and D3 resolver certificates.
- Two-state, migration and read-certificate laws: `DerivedColumn*`,
  `ReadCertificate*`, `MigrationQueryFrames`, `TwoStateAssertions`.
- `Sql.check`, `sql_run`, `sql_auto`, `AutoSearch` and the `mvcgen` integration.

## Measurement

Record in the status file, once at completion: lines deleted by this inventory,
lines added by the rule library and tactic, and the net change in maintained
Lean lines. Before/after counts are one-time acceptance work, not a CI check.
