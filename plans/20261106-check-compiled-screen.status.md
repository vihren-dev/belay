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
