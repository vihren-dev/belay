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

Moved the unused failed-state and plain-write frames to ReplacedFailureFrames.
ReplacedSchemaFailures and ReplacedReadPragma check the original group contracts.
The concrete CREATE and DROP examples use their computed error steps. The
read-only pragma example uses the shared query/prepare-error frame.
surface_schema_script_test checks the original premises, logical axioms and
concrete cases. Historical source links in the resolver inventory now point
at the original revision.
