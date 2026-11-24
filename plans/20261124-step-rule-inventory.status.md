# Exact step rule inventory

Created 2026-11-24. Status OPEN.

[Task](20261124-step-rule-inventory.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

The implementation spans Programs/Scripts in the model, the common send
rule and the SqlRun modules in the surface. The syntax SELECT contract
still applies without a resolution equation or a database validity proof.
The remaining general send uses in the tests are temporary witnesses or
tests of the old diagnostic.

Removed the general send fallback and ported its two original statements
to ReplacedGeneralSend. The earlier send witnesses use this test module.
The automation checks include a chosen output that supplies the row to
the postcondition. The remaining work includes the group-law inventory
and Nix acceptance before deleting the temporary witnesses.
