# Status: the SQLite model moves to `Belay.Sqlite.Model` (ADR 0016, D3)

Created 2026-10-21. Status: DONE.
Task file: [task](20261021-model-move.task.md).
Specification: [ADR 0016](../docs/adr-0016-model-and-surface.md), D3.

## Progress

- 2026-10-21: the task file. Base: the top of PR #205 (ADR 0018's claims).

- 2026-10-21: the move, made by a script (`build/agent-logs/move/move.py`, outside the
  repository, run on a clean working copy): 272 files of the model move to
  `packages/belay-sqlite-model/Belay/Sqlite/Model/`, `Belay/Sqlite/Model.lean` becomes
  `Model/Database.lean`, and the old names change in 120 other files (the other Lean packages,
  the engineering examples and their baselines, the kernel tests, the Nix build, the
  conformance tools and mutant anchors, the tests, CODEOWNERS, the justfile and the living
  documentation). In the ADRs only the link targets change, so that their links resolve.
  Checks: the Lean packages build; `just test-full` passes; the predictions of the 48 frozen
  corpora before and after the move are equal, byte for byte; no old name stays outside the
  historical records.

- 2026-10-21: the stack is on main after #204 and #205 merged. The script, run again on the
  new base, gives the same tree. The end checks pass: `just test-nix` (after two tests got the
  surface package of S1), `just test-scheduled` and `just runtime-package`; the predictions of
  the frozen corpora are unchanged. DONE.
