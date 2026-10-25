# Status: S7 proof-cost reporting, production

Created 2026-10-25. Status: IN PROGRESS. The six decisions were answered on
2026-10-25. Part 1 (collector) is done and gated; Part 2 (checker `--costs`,
baseline comparison, documentation) is the current work.
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
- 2026-10-25: review `20261025T160932Z-b6ce3490` of the corrected task file has
  no findings. The task waits for the owner's answers to its six decisions.
- 2026-10-25: decisions answered. Owner: 2 (the `--json` report is the baseline)
  and 3 (exit 1 for growth, a baseline entry without a completed record and a
  failed record; exit 2 for incompatible data, unreadable libraries and usage
  errors; new entries exit 0; `--costs` runs alone). Coordinator: 1, 4, 5 and 6,
  all as recommended. The owner also approved changing `CLAUDE.md` to name
  `just test-scheduled-checks`; the coordinator makes that change in a separate
  pull request, so this task does not edit `CLAUDE.md`. Phase 2 starts with the
  mutual-block evidence.
- 2026-10-25: Part 1, collector. New modules `Belay/Sqlite/ProofCost{Record,Trace,Pending}.lean`
  and `ProofCost.lean` (the module that a user imports; `import Belay` does not
  import it). The two handlers (`declaration`, `mutual`) carry `incremental`,
  run the handlers registered before them in Lean's order, and restore the
  state when one answers `unsupportedSyntax`. With the option `belay.proofCosts`
  off they call the next handler and store nothing. With it on, they set the
  native body trace options, take the body nodes, strip them from the command
  trace state and from the messages and traces of the proof tasks, and store a
  `Pending` entry. Records are made at export, so the compiled file exists only
  after a successful compile. Decision in the work: the names of a command's
  declarations come from the module's constants (`getLocalConstantInfos`
  before and after the command), not from the info trees, because the info
  tree of an asynchronous theorem is not complete when the command returns
  (bare `lean` probe: the binder list was empty in async mode and complete in
  sync mode). A pending entry keeps only the body nodes of a proof task, not
  its snapshot tree, so the trees can be freed. The prototype's test-only
  collector, reader and tests are replaced by `tests/surface/ProofCost{Reader,
  OtherHandler,Cases,Surface,TraceChecks}.lean`, `tests/proof_cost_support.py`
  and `tests/surface_proof_cost_collect_test.py`; layer rule 7 says that the
  closure of `Belay` does not contain the collector.
  Focused Nix run of the 21 proof-cost tests (`-k proof_cost` on the `surface`
  suite, not a gate): `/nix/store/l7cfpi1qdnnasx13rby3v4zq3dw0y4w0-sqlite-verifier-test-surface-1`,
  21 passed. The mutual block gives a record for each peer, in async and sync
  mode, in both orders; the overhead sample (three surface proof commands, sync)
  is 6,676,554 internal heartbeats without and 7,261,970 with collection.
- 2026-10-25: Part 1, review round 1 of 2fc6ae23 (`20261025T194925Z-2fc6ae23`):
  one must and two should, all fixed. Must (R11): the collector removed whole
  body subtrees, so traces that the user enabled (for example
  `trace.Meta.Tactic.simp.rewrite`) disappeared. It now splices each body node
  out and keeps its children, and drops the empty anonymous trace root; the test
  `test_traces_that_the_user_asked_for_stay` checks it in async and sync mode.
  Should (R12): the collect test and `tests/surface_layers_test.py` were over
  200 lines; the tests are split in collect, compat, automatic and layers files,
  and `tests/surface_layers_test.py` is as on the base. Focused Nix run of the
  23 proof-cost tests (not a gate):
  `/nix/store/ydkfbhi16i15jdw994j3nqpq72nv8hgr-sqlite-verifier-test-surface-1`,
  23 passed.
- 2026-10-25: Part 1, review round 2 (`20261025T195853Z-ad23bd8c`): one must
  (R5), fixed. `withoutBodyNodesIn` had a catch-all case; it now names the three
  leaf constructors, so a new `MessageData` constructor fails to compile.
- 2026-10-25: Part 1 gate, run on `15607f6d` (review `20261025T195931Z-15607f6d`:
  no findings). `just test-full`: test reports
  `/nix/store/hhpafzvbzh0dq6gygz9hilch1zszd6yb-sqlite-verifier-test-reports`
  (surface suite 332 passed, with the 23 proof-cost tests; other suites 480 and
  286 passed). `just verdict`:
  `/nix/store/gz1wg4l0969wpihb402jjayih440m13x-sqlite-verifier-verdict`.
  Part 1 (outcomes 1-9 and 13) is done; Part 2 (outcomes 10-12) is next.
- 2026-10-25: Part 2, pure report modules. New `Belay/Sqlite/ProofCost{Units,
  Report,Compare,Arguments}.lean`: budget units with three exact decimal places,
  the report of a library (`LibraryCosts.ofModules`, its JSON form that serves as
  the baseline, its text), the comparison with a baseline (exit codes 0, 1, 2),
  and the command line. None imports Lake or the collector, so
  `tests/surface/ProofCostCompareChecks.lean` runs them with `#guard`s, compiled
  by `tests/surface_proof_cost_compare_test.py`. Focused Nix run (not a gate):
  `/nix/store/ziklmsnchlh389zs9pvdql9balyzsski-sqlite-verifier-test-surface-1`,
  1 passed.
- 2026-10-25: Part 2, review round 1 of 445cbcbd (`20261025T202637Z-445cbcbd`):
  three musts and two shoulds, all fixed. R5: the status matches name every
  `ProofCostStatus` constructor. R11: a baseline entry without a count is not
  skipped; if the proof failed or is gone now, the run fails (guards added).
  R9 and R19: a docstring, and the opening of this file.
- 2026-10-25: Part 2, review of the refactor `41b7bcde` (`20261025T203438Z-41b7bcde`):
  one must (R11) and one should (R9), fixed. A baseline entry without a count
  also fails the run when the proof has no exact count now (guard added), and
  the fixture has a docstring. Focused Nix run of the 7 report and comparison
  tests (not a gate):
  `/nix/store/vraggxhp3znizyrxy0yig0l237jjci27-sqlite-verifier-test-surface-1`,
  7 passed.
