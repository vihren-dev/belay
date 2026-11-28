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
- 2026-11-28: the prototype `experiments/bag-results/Bags/` (17 files, 53 audited theorems,
  1,225 code lines) and the findings `experiments/bag-results/README.md`. Review
  20261128T135008Z-27cfc60e: the sqlite3 deadline has a name; two requests for tests of the
  experiment's own scripts rejected. Nix build
  `/nix/store/yrak1zfpf6m2ya1rincc2gjiw0gv5gsv-bag-results-experiments`: 18 Lean files compiled
  without warnings, 57 audited theorems on the standard axioms, probe output equal, kernel cost
  and per-file code lines recorded. Checks: this Nix build.
- 2026-11-28: review 20261128T140202Z-26e9a1e1 of the prototype: `toBag_rank` says which
  readers it covers, proof sketches for four long proofs, `max` under NOCASE is not an example
  of an order-free aggregate, the evaluation order of `select`. Nix build
  `/nix/store/yp3nx9fvvdb9ls9dzrwlmq51112m49b6-bag-results-experiments`: 57 audited theorems on
  the standard axioms, probe output equal, 1,246 code lines.
