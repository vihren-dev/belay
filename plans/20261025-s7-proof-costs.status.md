# Status: S7 proof-cost reporting, production

Created 2026-10-25. Status: task file written; waiting for the owner's answers
to its six decisions. Implementation has not started.
Task: [task file](20261025-s7-proof-costs.task.md).
Specs: ADR 0017 D1 (S7 row, "S7 cost clarification"); the
[findings](../docs/s7-proof-cost-findings.md); the completed
[prototype task](20261024-s7-proof-cost-prototype.task.md) and
[status](20261024-s7-proof-cost-prototype.status.md); the S7 files
[task](20261024-surface-s7-files.task.md) and
[status](20261024-surface-s7-files.status.md) for the shared checker.

## Relevant source (base `e384c875`, PR #260)

- Prototype collector: `tests/surface/ProofCost{Records,Collector,Cases,Surface}.lean`,
  `tests/proof_cost_test.py`, `tests/proof_cost_support.py`.
- Checker: `packages/belay/BelaySqlCheck.lean`, `Belay/Sqlite/SqlCheckReport.lean`,
  `Belay/Sqlite/SqlSourceRecord.lean`; layer rules in `tests/surface_layers_test.py`.
- S5 linter (read-only for this task): `Belay/Sqlite/SqlAutomatic.lean`,
  `CheckDeclarations.lean`.
- Registration: `packages/belay/lakefile.lean`, `tests/nix_suites.json`,
  `build-support/tests.nix`.
- Lean 4.34.1 sources: `Lean/Elab/Declaration.lean` (`elabDeclaration`,
  `elabMutual`), `Lean/Elab/MutualDef.lean` (`elabFunValues`),
  `Lean/Elab/Command.lean` (`elabCommandUsing`), `Lean/Elab/Term.lean`
  (`incrementalAttr`).

## Progress

- 2026-10-25: read the accepted contract, the findings and the S5/S7 code at
  `e384c875`. Two diagnostic probes with the prototype collector and plain
  Lean 4.34.1 (not Nix evidence): a `mutual` block of two theorems gives no
  record with the prototype hook; adding a `mutual` handler that delegates to
  `elabMutual` gives both records. The prototype also leaves the native trace
  line in the compiler output. Wrote the task file with six owner decisions
  (installation, baseline file, failing conditions, stale compiled files,
  other handlers, unmeasured inventory).
- 2026-10-25: review `20261025T160753Z-0bf2dd32` of the task file had four
  musts (all R19): the source hash cannot detect a failed rebuild caused by
  imports or options; instrumentation can exhaust `maxHeartbeats`, so message
  equality needs that exception; the task-end command differs between
  `CLAUDE.md` (`just test-scheduled`) and the owner's rule
  (`just test-scheduled-checks`); the trace label is a formatted message, not a
  `Name`. The task text now states each point.
