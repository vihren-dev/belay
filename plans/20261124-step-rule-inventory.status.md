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
