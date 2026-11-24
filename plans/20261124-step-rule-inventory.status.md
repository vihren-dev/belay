# Exact step rule inventory

Created 2026-11-24. Status OPEN.

[Task](20261124-step-rule-inventory.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

The implementation spans Programs/Scripts in the model, the common send
rule and the SqlRun modules in the surface. The syntax SELECT contract
still applies without a resolution equation or a database validity proof.
The remaining general send uses in the tests are temporary witnesses through ReplacedGeneralSend.

Removed the general send fallback and ported its two original statements
to ReplacedGeneralSend. The earlier send witnesses use this test module.
The automation checks include a chosen output that supplies the row to
the postcondition. The remaining work includes the group-law inventory
and Nix acceptance before deleting the temporary witnesses.

The remaining callers of the general single-execution send equivalence were
ReplacedColumnIfOk, ReplacedSendLaws, ReplacedUpdateSendLaws and ReplacedDeleteSendLaws. Its original statement and proof
now live in ReplacedGeneralSend with an axiom audit. SqlRun, SqlRunRules
and SqlRunGoals implement the diagnostic and read traversal. KindRuleSend
contains the common rule. The affected suites are surface_schema_script_test
and surface_s6_automation_test.

Moved the failed-state and plain-write frames used only by retention proofs to ReplacedFailureFrames.
ReplacedSchemaFailures and ReplacedReadPragma check the original group contracts.
The concrete CREATE and DROP examples use their computed error steps. The
read-only pragma example uses the shared query/prepare-error frame.
surface_schema_script_test checks the original premises, logical axioms and
concrete cases. Historical source links in the resolver inventory now point
at the original revision.

The D5 example identifies the pilot revision. Each group witness names the model laws it checks.

ReplacedOrdinaryFrames proves five original contracts: the nonquery
no-error projection, the unmodeled-error frame, the ordinary database
frame, and both IF NOT EXISTS congruences. The conditional CREATE fixture
uses the general equal-resolution congruence directly. The derived-column
backfill uses the full successful UPDATE equation, and CREATE TRIGGER
uses the prepare-error and creation equations. surface_schema_script_test
checks the retention, and surface_derived_column_test checks the installed
guide example and the derived-row claims.

The group-frame test identifies the four laws used in ReplacedOrdinaryFrames.

The nonquery choice projection only had callers in the former write and
send witnesses. ReplacedNonQueryOutputs now supplies it to those fixtures
and audits both original formulas. ReplacedBackfill checks the former
backfill_step contract. Its sole package caller, derivedColumn_state in
DerivedColumnScript.lean, now uses runScriptStep_plainUpdate_eq and
Connection.afterWrite_backfill. That data fact identifies the stored rows
and published counters for an assignment without referring to a script step.

The backfill data contract now states its row-free context and its quantification over caller inputs and reached counters.

The certificate for a read of one table now describes its scan rows, full
connection and absence of further executions. ReadCertificate.output_eq
compares these scans across every reached branch. Preservation and
commutation in ReadCertificatePreservation and CertifiedQueryCommutation use
the actual steps. KeptRead.preserves consumes scan evidence before and after
the migration. Its static checker accepts a comparison read whose steps
match the actual read's. The README rebuild uses its sessions read for both.
The singly executed observation rules now take an actual absence of further
executions. DerivedColumnQueries and the certificate callers supply it.

ReplacedCertificateObligations, ReplacedCertificateClaims and
ReplacedCertificateChecks audit the three old frames, five migration claims,
original schema checker, single-statement observations and the former
runScriptStep_simpleTable_output_append. CatalogOutputCases checks a write
with RETURNING on an empty table with zero counters against a full scan
certificate. CertificateAfterDrop, S6RulesQueryPattern, S6RulesNegativeReads
and S6RulesNegativeCertificates check moved tables, a widened SELECT star
and an unmodeled schema read. The sql_commute diagnostic describes the scan.

KeptReadChecks uses distinct parameter bindings for the read and its reference. The checker contract documents this and its success domain. The scan obligations name the two table positions and the moved certificate.

Site.LookupMove and Site.ReadPreserved compare the output of each actual statement
with a calm one-table scan on the corresponding catalog. Their callers in
DerivedColumnReads and DerivedColumnReadCheck use output witnesses.
The model's two derived-column output laws and resolvedStepOutput_simpleTable_agree
compare scan data. ReplacedSiteOutputs, ReplacedSiteCertificates and ReplacedSiteClaims
check the earlier model laws, certificate constructors, preservation and translation
claims. LowercaseQueries, ConcatExpansion and S6ColumnLookups exercise real callers.

The derived-column schema checker now checks a reference for the actual read and
transports its scan outputs. The single and parameter-family proof rules, the
computed certificate, sql_auto, the agent guide and skill use this contract.
ReplacedSiteCheckers audits both original formulas. DerivedColumnOnSchema also
proves preservation for an arbitrary read with the named-column scan's outputs.

ReplacedExecutionProjections recovers the two singleton projections
(runScriptStep_executions, runScriptStep_others_of_single) and SELECT connection
and alternative projections (runScriptStep_select_connection, runScriptStep_select_others).
The concrete AddCustomerClaims and the syntax-only row law use the combined
SELECT frame, which covers queries and prepare errors. DerivedColumnQueries uses
the shared execution list. The schema and SELECT fixture chains audit the original four contracts.

A row output excludes a stopped step for any kind. RunStep.eq_of_rows combines
this data fact with the caller's continuing frame. It replaces both SELECT-row
step projections. The positive and negative rowid-alias equivalences now accept
the actual frames. ReplacedExecutionProjections and ReplacedSubqueryEquivalence
check the former contracts. LowercaseSimulation and S6NotBlockedLaw use the
common SELECT frame in their end-to-end migration and rowid proofs.

SelectSyntaxFrame supplies the shared SELECT frame to the two rowid-equivalence checks. The public statement lists each frame, query, parameter and table premise.

## D12 step-law inventory

This inventory uses the kernel theorem types and a separate source search through all packages. It counts authored declarations, including private theorems. It excludes generated equation, projection and constructor theorems. In this table an unqualified name beginning with `runScriptStep` is in `Belay.Sqlite.Model`.

| Group | Theorems that name the step | Use across kinds |
| --- | --- | --- |
| Ordinary effects | `runScriptStep_effect`, `runScriptStep_execution_effects`, `runScriptStep_ordinary_ok` | The frame callers use ordinary reads and writes. DerivedColumnSuccess needs the successful ADD COLUMN and the subsequent UPDATE. ExecutionEffects also handles each alternative write. |
| One execution when the resolved statement is outside the source-write group | `runScriptStep_others`, `ScriptConditionsWith.single_step` | ReadOnlyFrame and PlainWriteFrame need the empty tail for reads and writes. ScriptSuccess and SendStatementsBranches carry it through mixed scripts. |
| Plain writes, source writes and sheltered positions | `runScriptStep_plainWrite_frame`, `runScriptStep_insertSelect_frame`, `Connection.shelter_step` | ShelterFrame and TableKeeps consume the INSERT, UPDATE and DELETE frame. TableKeeps and SchemaPathStep handle source writes with empty or nonempty RETURNING and with or without conflict clauses. The shelter applies to a distinct-target write and to a read. |
| Catalog paths | `runScriptStep_create_ok`, `runScriptStep_succeedsBySchema`, `runScriptStep_keepsTable`, `runScriptStep_tableAtPrefix` | SchemaSuccess handles CREATE TABLE, VIEW, TRIGGER and other schema-checked operations in scripts. The table-path callers in SendSchemaPath and RebuildKeepsInvariant follow multiple statements, including CREATE, row copy and DROP, through each execution. |
| Schema statements identified by input syntax | `addColumn_plain_step`, `createTrigger_step`, `runScriptStep_createIndex_plain_ok_iff` (private), `runScriptStep_createIndex_ok_iff` | DerivedColumnScript starts from successful runs on arbitrary admitted sites. The first two proofs need both the prepare-error equation and the corresponding successful DDL equation to recover that run's state. The index checks distinguish index creation, refusal and, for IF NOT EXISTS, an empty DROP. CreateIndexSuccess uses these distinctions to characterize success of SQL text on each catalog. |
| Read-only frames and SQL SELECT syntax | `runScriptStep_readOnly_keeps`, `runScriptStep_select_keeps`, `runScriptStep_select_output` | A prepared SELECT can be a query or a prepare error. QueryRule, SchemaSuccess and ControlStepExamples use both kinds. The result and error bridges in SelectResultBridge and SelectErrorBridge depend on the common frame and shape. SelectOutcomeCases covers the successful query and missing-table error. |
| Syntax-only SELECT checks | `Sql.check_query_select`, `Sql.check_single_select`, `Sql.check_send_select`, `check_query_returnsResult_iff`, `check_query_returnsError_iff`, `check_send_returnsResult_iff` | These checks admit modeled successes, modeled errors and failures to model execution. The sent-SELECT branch in runGoal (SqlRun.lean) remains under D10. The old sendRule dispatcher is deleted: syntax suffices to enter the continuation without a resolution equation or a valid-connection proof. The generic rule requires both. Query and single have their own program contracts. |
| Ordinary SELECT observation and single-read scripts | `Model.observeTwoState_ordinary`, `Script.observeTwoState_ordinary`, `Script.outputOn_isQuery` | TwoStateAssertions and the two-state examples compare ordinary SELECT execution with two-state observation, including restrictions and prepare errors. The single-read output bridge covers SELECT and read-only pragmas. |
| Application statements with comparison certificates | `DerivedColumnMigration.translatesAt_of_outputs`, `DerivedColumnMigration.preserves_of_check`, `DerivedColumnMigration.preserves_of_check_forall`, `KeptRead.preserves_of_check` | The translation compares actual outputs of two non-source statements. The high-level preservation relations require single read-only scripts (SELECT or a read-only pragma). The static checker can resolve a separate reference; the caller supplies agreement of the actual outputs or steps. |

**One kind.** `runScriptStep_copyOf` handles the application-level full-column copy used by table-rebuild's RebuildSucceedsCopy. It starts with rowid alias, type, key and target-emptiness conditions. It proves existence of the complete successful step, preservation of rowids in the copied main database, and the permutation property of **every** further connection, including the singleton-order case. A single branch or one row-data equality cannot establish that contract. The proof uses `runScriptStep_plainInsertSelect_eq` and the independent data theorem `runStatement_copyOf`.

**All kinds.** An actual error, row value, continuation, ready run, matching scan or table-path invariant is a property of an input or output. It does not specify its resolved kind. The following authored contracts in the kernel inventory have that form. In verifier-conformance, `runPassStep_matches` compares the conformance and model steps for arbitrary input syntax.

- Model: `runScriptStepFailure_continued`, `runScriptStep_congr_resolve`, `runScriptStep_continued`, `runScriptStep_continued_spec`, `runScriptStep_continues`, `runScriptStep_counters`, `runScriptStep_createdTables`, `runScriptStep_error_failure`, `runScriptStep_execution_runs`, `runScriptStep_executions_continue`, `runScriptStep_holds`, `runScriptStep_index`, `runScriptStep_of_clock_counter`, `runScriptStep_of_ne_clockUnmodeled`, `runScriptStep_output`, `runScriptStep_output_at`, `runScriptStep_output_of_resolved`, `runScriptStep_ran`, `runScriptStep_resolveState`, `runScriptStep_resolved`, `runScriptStep_valid`, `runScriptFrom_head_cons`, `successful_script_cons`.
- Programs: `Sql.Branch.continued_own`, `Sql.Branch.found_eq`, `Sql.Frame.exec`, `Sql.ScopedAt.of_row_steps`, `Sql.branch_continued_executions_iff`, `Sql.branch_continued_iff`, `Sql.branch_stopped_iff`, `Sql.check_continued`, `Sql.check_exec`, `Sql.check_query_of_step_rows`, `Sql.check_send_of_rule`, `Sql.check_stopped`, `Sql.succeedsFrom_continued`, `check_query`, `check_single_of_statement`, `sendStatements_branch_invariant`, `sendStatements_single_actual`, `sendStatements_single_branch`, `sendStatements_single_keeps`, `sendStatements_single_observations`, `sendStatements_succeedsFrom`, `sendStatements_succeeds_mixed`.
- Runs: `Run.query_mismatch`, `Run.query_overflow_calmTable`, `Run.query_prepareError`, `Run.query_returnsError_iff`, `Run.query_returnsResult_calm`, `Run.query_returnsResult_calmTable`, `Run.query_returnsResult_compound`, `Run.query_returnsResult_faultless`, `Run.query_returnsResult_iff`, `Run.query_returnsResult_select`, `Run.send_mustFail`, `Run.send_returnsError_iff`, `Run.send_returnsResult_iff`, `Run.send_returnsResult_select`, `Run.send_unready`. The specialized evidence compares an actual output with evaluated query or error data. The four result/error equivalences quantify over any single statement.
- Application state and observations: `DerivedColumnMigration.Site.LookupMove.outputs`, `DerivedColumnMigration.Site.LookupMove.rows`, `DerivedColumnMigration.Site.ReadPreserved.outputs`, `ReadCertificate.output_eq`, `ReadCertificate.step_keeps`, `Sql.EquivAt.of_select_steps`, `Sql.EquivAt.in_exists_of_rowidAlias`, `Sql.EquivAt.notIn_notExists_of_rowidAlias`. The original catalog, filter, rowid and NULL checks still apply to the comparison data. The actual statements supply their outputs or frames.

**Coverage and unfolds.** The 35 registered equations cover the pilot's two kinds, two more plain writes, four control/settings kinds, eight schema/prepare kinds, one query kind, two row writes and sixteen program/RETURNING modes. No kind gets a second equation. The direct step unfolds are in the kind-rule files, the all-kind guards, clock, counters, indices, continued-run and output laws, equal-resolution congruence and the conformance traversal law. Replay and alternative-execution examples also call the parameterized runner as data. The scan included the packages, tests and examples. No per-kind client unfolds the dispatcher.

The original one-send equivalence now proves the empty execution list directly
from the package. It will keep testing both directions on a context with no
validity proof. The positive IN/EXISTS witness will keep testing the absence
of a non-NULL premise on the inner column. Both final witnesses can stand alone.

## Retention evidence before deletion

Nix compiled and audited each module below at revision `8a898446a7e4a88b87f72869e7ef9d01844c73c4` (tag `adr-0033-retention-witnesses`). Its package contracts
include the last changes used by these proofs. Nix ran all eleven pytest owners of the temporary modules in the surfaceS6 and surfaceSelect derivations. Each original proof passed its ordinary-axiom check. The JUnit records contain the six expected schema/script owners and the five expected query owners. The suite outputs are `/nix/store/741wf1pv5ci4lhqa06abrad2wff4l03d-belay-test-surfaceS6-1` and
`/nix/store/mbvcgkgqzikw6356nki8s5v1bdx2qgiy-belay-test-surfaceSelect-1`. The accepted revision contains 48 retention modules and
143 audited declarations.

| Group | Accepted modules | Durable evidence |
| --- | --- | --- |
| Pilot and plain writes | `ReplacedDeleteSendLaws`, `ReplacedFailureFrames`, `ReplacedPlainWriteLaws`, `ReplacedSendLaws`, `ReplacedStepLaws`, `ReplacedUpdateSendLaws` | ItemInsertClaims, ItemInsertAnyClaims, PlainInsertStepCases, S6AutoEffects and schema/row-effect claims. |
| Control and settings | `ReplacedControlContinuation`, `ReplacedControlFrame`, `ReplacedControlSend`, `ReplacedSetting`, `ReplacedTransaction` | ControlSendClaims, ControlStepExamples and SchemaRuleExamples check active/idle and pragma transitions. |
| Schema and backfill | `ReplacedAddColumn`, `ReplacedBackfill`, `ReplacedCatalogContinuation`, `ReplacedCatalogRewrite`, `ReplacedCatalogSend`, `ReplacedColumnIfOk`, `ReplacedColumnSend`, `ReplacedConditionalCreation`, `ReplacedOrdinaryFrames`, `ReplacedPlainDrop`, `ReplacedSchemaFailures` | SchemaSendClaims, the rebuild and derived-column applications, check boundaries and native schema replays. |
| Query outcomes and rows | `ReplacedCalmRuns`, `ReplacedFailedRuns`, `ReplacedKeyCheck`, `ReplacedObservations`, `ReplacedOverflowRuns`, `ReplacedPragmaOutputs`, `ReplacedQueryOutputs`, `ReplacedRowPredicates`, `ReplacedSelectRuns`, `ReplacedReadPragma` | SelectOutcomeCases, SelectContextCases, QuerySendClaims and the execution, mismatch, overflow and pragma fixtures. |
| Context and certificates | `ReplacedCatalogRules`, `ReplacedCertificateChecks`, `ReplacedCertificateClaims`, `ReplacedCertificateObligations`, `ReplacedContextRules`, `ReplacedSiteCertificates`, `ReplacedSiteCheckers`, `ReplacedSiteClaims`, `ReplacedSiteOutputs` | CatalogOutputCases, KeptReadChecks, CertificateAfterDrop, DerivedColumnOnSchema, LowercaseSimulation, A21/A22, counter and NULL/stale-certificate checks. |
| Write modes and execution properties | `ReplacedExecutionProjections`, `ReplacedNonQueryOutputs`, `ReplacedProductionSuccess`, `ReplacedProgramDrop`, `ReplacedWriteChoices` | InsertWithRulesClaim, ProgramWriteClaims, ReturningWriteClaims, SourceWriteClaims, RowWriteSendClaims and the execution-branch checks. |
| Partial retention | `ReplacedSubqueryEquivalence`, `ReplacedGeneralSend` | Keep one validity-free send equivalence until another client audits both directions without a validity hypothesis. Keep one positive IN/EXISTS witness until a dedicated client checks nullable inner values without a non-NULL premise. The negative form has S6NotBlockedLaw. |
