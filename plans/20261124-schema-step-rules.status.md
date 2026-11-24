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

The slice review identified three proof sketches, two fixture descriptions and
obsolete tactic premise handling. Updated the texts and removed the obsolete
success and failure branches and the unused next-connection substitution.

The second review found a stale module description and a missing syntax
premise in the list that gates continuation traversal. The fallback now waits
for its notInsertSelect premise. S6AutoPaths exercises this open premise and
its discharge for a CREATE INDEX.

The fallback regression now checks the binders of its open reached goal,
so removing the notInsertSelect gate changes the fixture result.

At 22c62a48 the final simplification count is 98,589, including 59,128
model, 14,312 surface and 21,456 test code lines. The other scopes match
the start. Timings below are the faster of two elaborations in seconds.

| Changed sql_run fixture | Start | End |
| --- | ---: | ---: |
| S6AutoPaths | 51.80 | 50.74 |
| SchemaRuleExamples | 15.58 | 29.19 |
| SchemaSendClaims | new | 4.79 |

The regression check for the open fallback continuation is
test_sql_run_covers_every_statement_rule in surface_s6_automation_test.py.

The earlier setting witness in ReplacedControlSend now describes its proof
directly. Its former documentation reference named the removed DROP
surface rule. The complete verdict output matches slice 3 byte for byte
(store paths 88m86jvy8hk374zi93yjzb3a3animn5a and 7x0wipxb4j14x4pm411k64cjbw2r3awx).
After incorporating the checker allocation and control review, the start has 98,362 code lines. The schema rules at f9a36cf1 have 14,321 surface lines and 98,598 total. The three fixtures in the timing table contain the changed sql_run proofs.

The full suite exposed a proof-search regression after registering the DDL rules.
The default checker exhausted its budget on the existing UPDATE triple.
SqlRunGoals.hintedResolution now asks for the resolver's output before choosing
a rule. SqlRunKindRules applies the common send bridge once. When the resolution
can be inferred, each candidate compares its premise with that proof. Hints
that require a particular expected kind can still elaborate on the individual
candidate. The same original work budget and ordered rule set apply.
The affected suites are surface_s6_check_programs_test (including printed proof
replay), surface_s6_check_editor_test, surface_s6_automation_test and
surface_schema_script_test.
