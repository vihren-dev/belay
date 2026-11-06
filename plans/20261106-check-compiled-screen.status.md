# Status: `#sql_check` screens candidates with compiled code

Created: 2026-11-06. Status: OPEN.
Task: [20261106-check-compiled-screen.task.md](20261106-check-compiled-screen.task.md).
Design: ADR 0031, slice 2 (D2, D3 without D4, D5, D6, D8).

Sources: `packages/belay/Belay/Sqlite/CheckSamples.lean` (`visitCandidates`),
`CheckData.lean` (`dataValue`, `databaseValue`), `CheckRandom.lean`, `CheckOperation.lean`
(`check`), `CounterexampleWitness.lean` (`contradictAt`), `CounterexampleActual.lean`,
`CheckReplay.lean` (`shrinkProposals`), `CheckReplayData.lean` (`checkedConstruction`),
`ReplayConstruction.lean`, `CheckBudget.lean`, `CheckOptions.lean`, `CheckDisplay.lean`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: compiled data (`CheckCompiled.lean`: `compiledValue`, `awaitCompiled`,
  `checkCompiledClosure`, `withCompiledLimit`). `dataValue` and `databaseValue` compute with
  compiled code in a dedicated task and keep the kernel check; `normalizedData` is deleted.
  New option `sql.checkTimeLimit` (`SampleConfig.timeLimit`); an unknown result that the time
  limit stopped has its reason (`Outcome.reason`). `maxDataNodes` is 65,536. The closure rule
  treats every opaque constant outside Lean and `Belay` as partial, because Lean keeps a
  `partial` definition as an opaque constant. Tests: `surface_search_test`,
  `surface_check_readable_test`, `surface_check_default_budget_test`,
  `surface_check_real_schemas_test`, `surface_check_command_test`, `surface_sampling_test`,
  `surface_counterexample_test`, `surface_inference_test`, `surface_replay_test`,
  `surface_s6_check_programs_test`, `surface_s6_not_blocked_test`, `surface_automatic_test`,
  `surface_rebuild_test`.
