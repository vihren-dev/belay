# Status: a root Lake package, so that Reservoir can index Belay, and version 0.2.0

Created 2026-11-14. Task: `20261114-root-package-for-reservoir.task.md`. Owner request, 2026-11-14.
Status: OPEN.

## References

- Specifications: ADR 0006 (the model package), ADR 0010 section 7 (build categories), ADR 0016 D2
  and D3 (layers and names), ADR 0021 (the removed product and its tags), ADR 0023 fact 8 (Nix
  workspaces).
- The surface package: `packages/belay/lakefile.lean`, `packages/belay/lake-manifest.json`.
- Tests and helpers: `tests/test_lean_categories.py`, `tests/surface_support.py`,
  `tests/sql_file_support.py`, `tests/runtime_fixtures.py`, `tests/test_source_identity.py`,
  `tests/surface_layers_test.py`, `tests/test_nix_test_targets.py`.
- Nix: `build-support/default.nix`, `build-support/sources.nix`, `build-support/tests.nix`.
- User instructions: `README.md`, `examples/table-rebuild/README.md`,
  `skills/belay/templates/lakefile.toml`, `skills/belay/SKILL.md`, `packages/belay/README.md`.
- Reservoir: <https://reservoir.lean-lang.org/inclusion-criteria>; the indexer is in
  <https://github.com/leanprover/reservoir> (`scripts/testbed-analyze.py`).
- Prototype: jj change `mxzxnpzq` (local, not for merge).

## Progress

- 2026-11-14: prototype and owner decisions 1 to 5; task and status files.
