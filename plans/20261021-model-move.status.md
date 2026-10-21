# Status: the SQLite model moves to `Belay.Sqlite.Model` (ADR 0016, D3)

Created 2026-10-21. Status: OPEN.
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

## Remaining

- `just test-nix`, `just test-scheduled` and `just runtime-package`, with the checks of S1 at
  the end of ADR 0017's first slice.
