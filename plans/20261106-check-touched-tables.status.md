# Status: `#sql_check` fills only the touched tables

Created: 2026-11-06. Status: OPEN.
Task: [20261106-check-touched-tables.task.md](20261106-check-touched-tables.task.md).
Design: ADR 0031, slice 3 (D4, D7, the consumer-size fixture of D9).
Previous slice: [20261106-check-compiled-screen.status.md](20261106-check-compiled-screen.status.md).

Relevant source files: `packages/belay/Belay/Sqlite/SampleCandidates.lean`,
`SampleDatabases.lean`, `SampleScriptHints.lean`, `CheckSamples.lean`, `CheckDomain.lean`,
`CheckBudget.lean`, `ReplayConstruction.lean`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: touched tables and constraint rows (D4). `Sampling.statementTables` names the
  tables of SELECT, INSERT, UPDATE and DELETE from their hints, none for other statements;
  `Sampling.touchedNames` closes them over foreign keys (parents and children), triggers on
  touched tables and touched views. `inferredData` returns them; they are none (every table)
  when the claim has Lean code, an unsupported structure or a script that does not evaluate.
  `Sampling.candidates` empties the untouched tables in every candidate (`onlyTouched`,
  `touchedTargeted`), enumerates contents of the touched tables only, and applies
  `Sampling.constrainedCells` (NOT NULL fallback, parent keys, no repeated keys) to the contents
  and the seeded databases (`touchedDatabase`). Task item 2 is amended: the targeted rows are not
  changed (ADR D3 applies D4 to the contents). Tests: `surface_search_test`
  (`CandidateConstraints.lean`), `surface_check_screen_test`, `surface_check_real_schemas_test`,
  `surface_check_readable_test`, `surface_s6_check_programs_test`,
  `surface_check_default_budget_test`, `surface_sampling_test`, `surface_rebuild_test`,
  `surface_check_command_test`, `surface_counterexample_test`.
