# Status: ADR17 guide and integrated acceptance

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-adr17-guide-acceptance.task.md).
Specs: ADR17 and its accepted decisions; explicit ADR deferrals remain in force.

## Prerequisites

All required feature tasks and their Nix acceptance precede this final gate.
S4, query sources and FK work are active. S5, S7 files, editor and doc-block
tasks are specified. S6 production execution contracts are reviewed; remaining
S6 assertions/patterns/automation and S8 await their tasks. The owner accepted
observation views, contextual S8 pairing, the fresh-run helper and the separately
named interface-scoped simulation.
Proof-cost production needs the specified collector experiment.

The product default workspace contains earlier unpublished S2/S3 guide edits.
Published profile/header corrections and current S4 guide edits use separate
workspaces. Final publication must reconcile those relevant changes without
including unrelated private history or copying private contents publicly.

## Progress

- 2026-10-24: specified a final capability and guide audit, installed-consumer
  integration, proof checks and publication boundary. Review is pending.
  ADR17 remains OPEN; this task file claims no completed feature or test result.
- 2026-10-24: review `20261024T145218Z-e244461b` has no findings.
- 2026-10-24: review `20261024T145825Z-2e5e2ef5` found one should:
  update the task's conditional wording after the view and S8 decisions were
  accepted. The task now names those accepted contracts and the separate
  still-pending fresh-run helper decision.
- 2026-10-27: the task file is refreshed against the current state (section "State on 2026-10-27"):
  the done tasks, the open S6 tasks, the public stack, the private guide PR chain #6 to #9, the unpublished
  S2/S3 guide commits, and the list of recorded guide changes. Workspace `sqlite-verifier-guide-accept`
  on `tasks/surface-editor-part3`.
- 2026-10-27: workspace `sqlite-verifier-guide-accept` (jj workspace of the public repository), private guide
  workspace `sqlite-verifier-product-adr17-accept`. Item 3 of the migration-pattern remainder (the type-affinity
  data-loss example): the guide's example is a rebuild that copies a TEXT column `zip` into an INTEGER column. No
  existing check covers it: the derived-column examples store `a + b` in a TEXT column, which is a different case.
  `tests/surface/RebuildAffinity.lean` and `tests/surface_rebuild_affinity_test.py` (suite `surface`) add it. The
  kernel proves that the rebuild succeeds, that '01234' becomes the integer 1234 and 'n/a' stays text, that the
  rebuild does not preserve the query of both columns (`rebuild_not_preserved`), and that a copy into a STRICT table
  refuses 'n/a' with result code 19. Native SQLite 3.51.0 gives the same rows for the three runs and the column name
  in the error text of the STRICT copy. The local focused run is not Nix evidence: the Nix result is recorded in the
  final gates.
- 2026-10-27: the capability inventory on the tree of `tasks/surface-editor-part3` (#289) is below. The rebuild rows were filled in after the merge of the part 2 branch (PR #290). The guide
  examples were compiled in a private harness against the installed library of this tree. That harness is not Nix evidence.

## Capability inventory

Columns: "Declaration or tool" is the public name that users call. "Task" is the plan file that accepted the behavior.
"Test" is a file of a Nix suite in `tests/nix_suites.json` (`surface`, `surfaceChecks`, `surfaceS6`, `harness`). A test
that runs a Lean fixture checks the fixture's theorems with the kernel. A test that opens a Lean server checks the editor
output of a real server. Every row is implemented; no required row is a proposal. The explicit deferrals follow the table.

| Capability | Declaration or tool | Task | Test |
| --- | --- | --- | --- |
| S1: SQL text parsed while Lean elaborates | `sql`, `sql!`, `#sql`; text package `belay-sqlite-text` (`Translation`) | `20261021-surface-s1`, `20261021-sql-text-package` | `surface_parser_test`, `surface_translation_checks_test`, `surface_layers_test` (suite `surface`); suite `parserLibrary` |
| S2: concrete databases and runs | `Database`, `Database.Raw`, `Database.Admitted`, `db!`, `Database.run`, `Script`, `Output`, `Script.run_append` | `20261022-surface-s2`, `20261022-validity-atoms` | `surface_guide_test`, `surface_foreign_key_atoms_test` |
| S3: parameters, programs and runs | `Sql`, `send`, `query`, `single`, `Sql.run`, `Run`, `Env`, `Script.runUntilError` | `20261023-surface-s3`, `20261023-parameters`, `20261018-clock-parameter` | `surface_parameters_test`, `surface_programs_test` |
| S4: claims over every database | `Holds`, `Succeeds`, `Succeeds.iff_ensures`, `Holds.iff_selectOne_count`, `Holds.iff_selectOne_tableInfo`, `Holds.reached_iff_holds_of_valid` | `20261024-surface-s4`, `20261024-s4-observations`, `20261024-s4-schema` | `surface_claims_test`, `surface_success_test`, `success_theorems_test`, `surface_schema_claims_test`, `surface_views_test` |
| S5: checked counterexamples | `#sql_check`, `sql_refute`, the background check, replay (`Replay.scriptReport`) | `20261024-surface-s5` | `surface_check_command_test`, `surface_search_test`, `surface_sampling_test`, `surface_counterexample_test`, `surface_inference_test` (suite `surfaceChecks`); `surface_replay_test`, `surface_automatic_test`, `surface_automatic_editor_test`, `surface_automatic_cancel_test` |
| S6: complete-execution equivalence, branches, weakest preconditions | `Sql.Equiv`, `Sql.EquivAt`, execution views | `20261024-s6-execution-contracts`, `20261024-s6-before-context` | `surface_execution_test`, `surface_execution_views_test`, `surface_two_state_test` |
| S6: fresh-run claims | `FreshEnsures`, `FreshEnsuresFrom`, `ifOk`, `andOk`, `holdsSince` | `20261024-s6-assertions`, `20261026-global-signup-invariant` | `surface_assertions_test`, `surface_assertion_examples_test` |
| S6: migration patterns | `Migration.QueryPreserves`, `QueryTranslates`, `Commutes`, `CommutesAs`, `Migration.after`, `quiet`, the `preserves`, `translates` and `commutes with` notation | `20261024-s6-migration-patterns` | `surface_migration_patterns_test`, `surface_migration_examples_test`, `surface_rebuild_affinity_test` |
| S6: effect rules, frames and automation | `sql_auto`, `sql_run`, `sql_commute`, `Sql.check_send_plainInsert` and the other `check_send_*` rules | `20261024-s6-automation` (part 1) | `surface_s6_automation_test`, `surface_s6_rules_test`, `surface_s6_check_programs_test`, `surface_s6_auto_editor_test`, `surface_s6_check_editor_test` |
| S6: query laws | `NOT IN` and correlated `NOT EXISTS` laws; the derived-column migration laws (`DerivedColumnMigration`) | `20261027-not-in-subquery-laws`, `20261027-derived-column-laws` | `surface_s6_not_blocked_test`, `surface_derived_column_test` |
| S6: schema, transaction and pragma statements, the table rebuild | the step, frame and success laws of CREATE TABLE, DROP TABLE, rename, BEGIN, COMMIT and the pragmas; `Migration.translatesAt_of_observations`; `sendStatements_succeedsFrom`; the guide's rebuild in `tests/surface/Rebuild*.lean`: `requireName_preserves_allSessions`, `requireName_succeeds` and `wrong_rebuild_loses_sessions` (`sql_refute`) | `20261024-table-rebuild`, `20261027-schema-script-laws`, `20261024-s6-automation` (part 2 on PR #290) | `surface_schema_script_test`, `surface_rebuild_test` (suite `surfaceS6`) |
| S7: SQL in files | `sql_file`, `sql_module`, the Lake `needs` inputs, the package-root option | `20261024-surface-s7-files` | `surface_sql_files_test`, `surface_sql_file_forms_test`, `surface_sql_file_root_test`, `surface_sql_records_test`, `surface_sql_lake_inputs_test` |
| S7: build freshness | `lake exe belay-sql-check` | `20261024-surface-s7-files` | `surface_sql_check_test`, `surface_sql_check_roots_test` |
| S7: proof costs | `import Belay.Sqlite.ProofCost`, option `belay.proofCosts`, `belay-sql-check --costs` with `--json`, `--baseline` and `--allowance` | `20261024-s7-proof-cost-prototype`, `20261025-s7-proof-costs` | `surface_proof_cost_collect_test`, `surface_proof_cost_compare_test`, `surface_proof_cost_report_test`, `surface_proof_cost_compat_test`, `surface_proof_cost_automatic_test`, `surface_proof_cost_layers_test` |
| S8: interfaces and simulation | `Calls.Signature`, `Calls.Interface`, `Calls.Pairing`, `Application`, `Simulation`, `ScopedSimulation`, the `simulates` notation | `20261024-surface-s8` | `surface_application_test`, `surface_application_syntax_test` |
| Editor: hovers, name corrections, origins, order warnings | `sql.orderWarnings`; the Lean server information of `sql!`, `db!`, `#sql` and `INSERT ... SELECT` | `20261024-surface-editor` (parts 1 to 3) | `surface_editor_test`, `surface_editor_tables_test`, `surface_editor_origins_test`, `surface_editor_executed_test`, `surface_editor_order_test`, `surface_editor_names_test`, `surface_editor_corrections_test`; suite `surfaceChecks`: `surface_editor_insert_tables_test`, `surface_editor_insert_order_test`, `surface_editor_renames_test`, `surface_editor_insert_names_test`, `surface_editor_rebuild_test` |
| Checked SQL doc blocks | the `sql` documentation block (`SqlDocBlock`) | `20261024-sql-doc-blocks` | `surface_sql_doc_blocks_test`, `surface_sql_docs_test` |

Explicit deferrals of ADR 0017 stay deferred: `withTransaction` (the model has no `SAVEPOINT`), the choice of profile in `Env`,
`random()` and `randomblob()`, the name of a failed constraint in a `db!` error for a write that runs a trigger or checks foreign keys,
and the table-valued pragma functions other than `pragma_table_info` and `pragma_foreign_key_list`. This task adds no deferral. The
model suites and the frozen verdicts that sit below the surface are not repeated here.

What the tests do not check: the examples in the private guide. The private record names the commands that compile them. The
editor rows check the output of a real Lean server and not the screen of an editor. The proof-cost rows check the report and its
comparison and not a user's own growth bound.

## Dispositions of the recorded guide changes

Each change is applied in the private guide. The private record names the checks. A change that was already correct in the guide is
marked as such.

| Recorded change | Disposition |
| --- | --- |
| Fresh-run purge frame claim with the two-state assertion and the captured start; the text-time counterexample; the `NOT` trap (`20261024-s6-assertions`) | Applied. |
| Order warning for `INSERT ... SELECT` and `LIMIT` without `ORDER BY` (`20261024-surface-editor`) | Applied. |
| Write claims through the expansion triggers are checked instances (`20261024-surface-s8`) | Applied. |
| Premises of `notBlockedIn ≈ notBlockedEx` (`20261027-not-in-subquery-laws`) | Applied. |
| Moved modules and renamed theorems of the derived-column laws (`20261027-derived-column-laws`) | Applied. |
| Rebuild: foreign keys are off on a new connection, `requireName` preserves `allSessions` for the guide's schema only, `requireName` does not abort on `PRAGMA foreign_key_check` rows (`20261024-s6-automation`) | Applied, with part 2 (merged from `tasks/schema-script-laws-part2`, `8b04d70a`). |
| Part 2 guide changes (a) to (c) of `20261027-schema-script-laws`: the unsafe rebuild needs `PRAGMA foreign_keys = ON` first; the preservation and success claims state the guide's schema (and `NoNullName`) as premises; `foreign_key_check` rows do not stop the commit | Applied. The guide uses `requireNameWrongEnforced`, `requireName_preserves_allSessions`, `requireName_succeeds`, and the replays `withoutName` and `dangling`. |

## Generalization of the new statements

This task adds one public theorem group: `tests/surface/RebuildAffinity.lean`. Its subject is a false universal claim of the
guide, so one witness database is the right form of the evidence; the general statement is not needed to refute it. The statement
that the copy stores `Value.store` of the new column affinity for every copied cell is the general form of `rows_after`. It belongs to
the rebuild laws of part 2 of the schema-script task. This task does not duplicate it. `rebuild_not_preserved` is stated for the weak
`Migration.QueryPreserves` on the database `addresses`, with the complete environment of the fixture: a fixed database is the least
that a counterexample needs, and the fixture states the premise `⟨rfl, rfl, rfl, rfl⟩` of the environment explicitly.
