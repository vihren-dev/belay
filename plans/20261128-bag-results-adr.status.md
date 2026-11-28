# Status: experiments and ADR for query results as bags

Created 2026-11-28.
Task: [20261128-bag-results-adr.task.md](20261128-bag-results-adr.task.md).
Status: IN PROGRESS.

Relevant sources: `packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Execution/Output.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Execution/PossibleResults.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/Queries/Evaluation/PossibleResults.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Dispatch/PossibleResultsExamples.lean`.

## Progress

- 2026-11-28: task and status files.
- 2026-11-28: review round 2 of the task: negative LIMIT, the order of a FROM subquery, and the
  line count of the prototype.
- 2026-11-28: review round 3 of the task: sort keys that fail, and FROM subqueries in a join.
- 2026-11-28: review round 4 of the task: no findings.
- 2026-11-28: experiments: `CurrentOutputs.lean`, the native probes P0 to P16, the kernel cost
  measurement, and `check.py` with `default.nix`. Nix build
  `/nix/store/2d2xyfsmjx1z8g3l21wi08x4w2ivrdm8-bag-results-experiments`: `CurrentOutputs`
  compiled with 3 audited theorems on the standard axioms, the probe output equals
  `probes/probes.expected`, kernel cost for 10, 50, 100 and 200 rows. Checks: this Nix build.
- 2026-11-28: review of the experiments: audit `byName_eq`, require exit status 1 of the probe
  run, report only the forbidden axioms, name the deadlines, describe the cost baseline. Nix
  build `/nix/store/gn0rarazw0rkw2n42zpb6d4i2d0c9fxc-bag-results-experiments`: 4 audited
  theorems, probe output equal, kernel cost recorded.
