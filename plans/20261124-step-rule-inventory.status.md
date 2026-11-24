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
