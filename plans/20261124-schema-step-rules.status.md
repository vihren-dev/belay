# Exact steps for schema changes and prepare errors

Created 2026-11-24. Status OPEN.

[Task](20261124-schema-step-rules.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

2026-11-24. Traced the eight schema and refusal branches in Execution.lean,
StatementStep.lean and Output.lean. Slice 4 follows the control rules.

The new equations cover the eight kinds in D10. The catalog success and
table-preservation proofs in CreateSchemaSuccess, TableKeeps and SchemaSuccess
use the equations. SchemaFailureLaws and AddColumnPlainStep handle prepare
refusals and successful steps through their respective rules. The write-rule
DROP remains separate until slice 7. The send tactic now uses the registered
rules for ADD COLUMN, plain DROP and rename.

| Witness in tests/surface/Schema/Tests | Original declarations |
| --- | --- |
| ReplacedPlainDrop | runScriptStep_drop_plain, runScriptStep_drop_frame, runScriptStep_dropTable_frame |
| ReplacedCatalogRewrite | runScriptStep_rewrite |
| ReplacedCatalogContinuation | runScriptStep_drop_continues, runScriptStep_rewrite_continues, runScriptStep_drop_ok, runScriptStep_rewrite_ok_of_outline, runScriptStep_rewrite_ok, runScriptStep_dropColumn_ok |
| ReplacedConditionalCreation | runScriptStep_noOp, runScriptStep_createTable_noOp, runScriptStep_createIndex_noOp |
| ReplacedAddColumn | addColumn_database, runScriptStep_addColumn_failed |
| ReplacedCatalogSend | Sql.check_send_dropPlain, Sql.check_send_rewrite |
| ReplacedColumnSend | Sql.check_send_addColumn |
| ReplacedColumnIfOk | Sql.ifOk_send_addColumn |

SchemaSendClaims checks the eight observable outcomes on a variable connection,
including a colliding unique index, a restricted default and a preparation
error. The migrated fixtures are SchemaDropExamples (parent removal and child
frame), CertificateAfterDrop (certificate obligations), ClaimsConditionalCreation
(kept table and index), S6RulesEffects (add_note_keeps_old_cells), S6AutoPaths
(widen_adds_null_cells) and SchemaRuleExamples (rename succeeds).

At the start the scc package and test counts are 59,132 model, 14,481 surface,
1,945 SQL text, 1,042 conformance, 134 documentation tool, 21,047 tests and
572 other (98,353 total). At the first implementation revision these are
59,128 model, 14,326 surface and 21,453 tests (98,600 total). Other counts
are unchanged. The retained laws cover schema changes, statement execution,
conditional creation and surface sends. No mutant table changed.
