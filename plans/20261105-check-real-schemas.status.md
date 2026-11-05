# Status: `#sql_check` on the tables a developer has

Created: 2026-11-05. Status: IN PROGRESS.
Task: [20261105-check-real-schemas.task.md](20261105-check-real-schemas.task.md).
Issues: #318, #293. Design: ADR 0031, D3 and D6 as amended.

Sources: `packages/belay/Belay/Sqlite/ReplayConstruction.lean` (`schemaRowsSql`),
`CheckReplayData.lean` (`checkedConstruction`), `SqlSource.lean` (`schemaSourceKey`),
`CheckData.lean` (`generatedExpr`), `CheckSamples.lean`, `CheckReplay.lean`
(`shrinkProposals`), `SampleDatabases.lean` (`suppliedVariants`), `CheckInputs.lean`.

## Progress

- 2026-11-05: task and status files.
- 2026-11-05: construction from the schema text (`Replay.schemaRowsSql`, `schemaSourceKey`,
  `generatedExpr`), the variants of supplied rows (`Sampling.suppliedVariants`), and `db :=` as
  the search schema (`elaborateInputs`). New fixture `CheckRealSchemas` with
  `tests/surface_check_real_schemas_test.py` (suite `surfaceChecks`): the four schemas of #318
  and the claim of #293 are false at the default budget. Capability change in an existing
  fixture: `equiv-false` of `S6CheckPrograms` (`with (db := sample)`) now reports a shrunk
  database (quantity 2) instead of `sample`, because the shrunk database now replays from the
  schema's text; `equiv-shrink-exhausted` needs the budget 100000 (not 200000) for the shrinking
  to run out. `tests/surface_s6_check_programs_test.py` checks the difference of the two runs
  instead of fixed quantities for that claim. Tests run: as in the status of #317 (the same
  tree), with `surface_check_real_schemas_test`.
