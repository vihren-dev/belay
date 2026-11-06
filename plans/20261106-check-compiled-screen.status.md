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
- 2026-11-06: compiled screen and candidate order (`CheckScreen.lean`: `screenTerm`,
  `compileScreen`, `firstAccepted`; `SampleCandidates.lean`: `Sampling.candidates`). For each
  value, `visitCandidates` tries the empty database and the named databases, then screens the
  candidates in batches of `screenBatch` in a compiled task and certifies each accepted one.
  `SampleConfig.screen` lets a caller supply a screen. A claim without a screen records the
  reason. `CheckRandom.lean` (the cooperative draws) and `targetedData` are deleted;
  `Sampling.selectCells` loses its resource-check parameter. `sql.checkCandidates` is 10,000.
  Targeted databases with more than `sql.checkMaxRows` rows in a table are skipped, as before.
  Capability changes: `CounterexampleCheckOptions.lean` (`one-random`, seed 12, one sample) is
  now `false`, because the table contents of the boundary values contain the row `-1`; the
  fixture now needs the two-column row `(-1, NULL)`, which only the random databases contain.
  New tests: `surface_check_screen_test` (accept-all screen, `implemented_by` claim with its
  reason and its explicit witness, slow screen at the time limit). Fixture claims of
  `surfaceChecks` and `surfaceS6` whose screen does not compile: the `implemented_by` claim of
  `CheckScreenFixture.lean` (intended), and the claim of `S6CheckPrograms.lean` that quantifies
  the result of a run (`∀ k, k + 1 = 0` on `send bump`: the screen has no input for the
  result); its test result is unchanged. Tests: `surface_check_screen_test`, the tests of
  `surfaceChecks` and `surfaceS6`, `surface_automatic_cancel_test`, `surface_rebuild_affinity_test`,
  `surface_claims_test`, `surface_replay_test`.
- 2026-11-06: review fixes: `Sampling.candidates` checks its limit before the table contents;
  the docs describe the selection of values before affinity and rowid assignment.
- 2026-11-06: shrinking by screening (D5). `visitCandidates` gives its callback the screen and
  the value of a witness; `check` shrinks with `screenedShrinkProposal` (`shrinkScreened`: at
  most `sql.checkShrinkAttempts` steps, each to the first proposal that the screen accepts) and
  certifies only the result, so a check certifies at most two witnesses. A claim without a
  screen keeps the certified shrinking (`shrinkCertified`). Capability change: the shrinking of
  `equiv-shrink-exhausted` (`S6CheckPrograms.lean`) now finishes at 100,000 units; the case
  now uses 30,000 (it finishes at 45,000, and runs out at 35,000 and 25,000), so it still
  checks that a shrinking that runs out keeps the refutation. Tests:
  `surface_check_screen_test` (a shrink that the kernel rejects keeps the original witness),
  `surface_check_command_test`, `surface_check_readable_test`, `surface_counterexample_test`,
  `surface_search_test`, `surface_check_default_budget_test`, `surface_check_real_schemas_test`,
  `surface_rebuild_test`, `surface_s6_check_programs_test`, `surface_inference_test`,
  `surface_sampling_test`, `surface_automatic_test`.
