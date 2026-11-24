# Exact steps of transaction control and setting pragmas

Created 2026-11-24. Status DONE.

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

The historical target rows link to the pilot revision and preserve the
original lists alongside dated slice 3 migration notes.

At the start revision the simplification-goal counter reports 59,296 model,
14,574 surface and 20,745 test code lines, 98,308 lines total. At a3722017
the corresponding counts are 59,132, 14,481 and 21,047, 98,353 total. Both
counts include 1,945 SQL text, 1,042 conformance, 134 documentation tool
and 572 other lines. ControlSendClaims is the only changed fixture whose
sql_run proof text changes. It is new, and elaborated in 1.85 s at the end
(faster of two runs). The Nix verdict at the start
(ij7ch4wx5cbhrfw2bgqdqzka346kx288-belay-verdict) and end
(88m86jvy8hk374zi93yjzb3a3animn5a-belay-verdict) compared byte for byte.
No mutant table changed.
After incorporating the checker allocation at 5ca0e596, the start has 14,583 surface lines and 98,317 total. The control changes have 14,490 surface lines and 98,362 total. The model and fixture counts above still apply.

The completed control slice uses 3af5b4d8 through 41457d43. Nix accepted the full suite in `pq7799f0zhyrsf9x573hy0h8z3956cz5-belay-test-reports`. The accepted verdict `88m86jvy8hk374zi93yjzb3a3animn5a-belay-verdict` matches the plain-write verdict byte for byte.
