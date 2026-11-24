# Exact steps of transaction control and setting pragmas

Created 2026-11-24. Status OPEN.

[Task](20261124-control-step-rules.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

2026-11-24. Read the transaction branches of SqlAdvance.lean and the existing
control and pragma laws. The starting revision for acceptance is the final
revision of slice 2.

The proofs of the four equations specialize resolution and compute the step.
The rule for ROLLBACK restores the saved database, clears the snapshot and
keeps the counters. The setting rule installs the value given by resolution.

The following replaced declarations have witnesses with their original
premises. Each witness is in tests/surface/Schema/Tests.

| Fixture | Replaced laws |
| --- | --- |
| ReplacedTransaction | runScriptStep_begin_idle, runScriptStep_begin_active, runScriptStep_commit_active, runScriptStep_commit_idle |
| ReplacedControlFrame | runScriptStep_begin_frame, runScriptStep_commit_frame, runScriptStep_setting_frame |
| ReplacedSetting | runScriptStep_setting, runScriptStep_pragma_foreignKeys |
| ReplacedControlContinuation | runScriptStep_setting_continues, runScriptStep_begin_continues, runScriptStep_commit_continues, runScriptStep_setting_ok, runScriptStep_begin_ok, runScriptStep_commit_ok |
| ReplacedControlSend | Sql.check_send_begin, Sql.check_send_commit, Sql.check_send_setting |

TableKeeps.lean moves runScriptStep_keepsTable. SchemaSuccess.lean moves
runScriptStep_succeedsBySchema. ControlStepExamples.lean moves the proofs
begin_snapshots_the_database, begin_active_keeps_the_connection,
commit_active_closes, commit_idle_keeps_the_connection,
pragma_turns_enforcement_on and pragma_inside_a_transaction_is_ignored.
ControlSendClaims.lean checks all four kinds over a variable connection.
The program of SchemaRuleExamples exercises the six-statement-kind script.
The retention and client fixtures cover M11, M12 and surface sends.
The relevant suites are surface_schema_script_test.py and surface_rebuild_test.py.

Registered both new Nix fixture roots and corrected the witness proof sketch and task background after review.

Repaired links in the resolver and query-observation records after the
full source checks found two references to deleted control modules.
