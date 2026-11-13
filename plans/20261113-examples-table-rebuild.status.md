# Status: the table-rebuild example as a Lake project under `examples/`

Created 2026-11-13. Task: `20261113-examples-table-rebuild.task.md`.

Relevant files: `README.md`, `tests/surface/Schema/Tests/RebuildExample.lean` and the `Rebuild*`
proof modules under `tests/surface`, `tests/surface_rebuild_test.py`, `tests/surface_support.py`,
`build-support/tests.nix`, `tests/test_lean_categories.py`, `docs/guide/agents.md`,
`skills/belay/SKILL.md`.

## Progress

- 2026-11-13: task written. Tried the library's tactics on `fixed_keeps_sessions` in a project that
  requires Belay by path: `sql_auto` (all routes fail), `sql_commute` after `intro` (only
  `Migration.PreservesAt`), `#sql_check` with budget 500000 (`unknown`). The proof moves.
