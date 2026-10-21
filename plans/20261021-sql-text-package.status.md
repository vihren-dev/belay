# Status: one SQL translation, the text package below the surface

Created 2026-10-21. Status: OPEN.
Task: [task file](20261021-sql-text-package.task.md).
Specification: [ADR 0017](../docs/adr-0017-user-surface.md), D2 and D6;
[ADR 0016](../docs/adr-0016-model-and-surface.md), D2; all with their amendments of 2026-10-21.

## Relevant files

- The text package: `packages/belay-sqlite-text/Belay/Sqlite/{ParserLibrary,Parse,ParseTree,Grammar}.lean`,
  `Belay/Sqlite/Translation/`, `c/parser_shim.c`, `lakefile.lean` (moved from `packages/belay`).
- The Python translation and binding: `belay/sqlite/syntax*.py`, `sql_tree.py`, `parser_library.py`, `located.py`.
- Callers: `conformance/predict.py`, `generated_program.py`,
  `native_fixture.py`, `native_replay.py`, `native_trace.py`, `progress.py`, `record_parser.py`,
  `replay_tiers.py`, `restriction_examples.py`.
- Builds: `build-support/default.nix`, `sources.nix`, `lean-package.nix`, `tests.nix`.
- Tests: `tests/syntax_*_test.py`, `tests/runtime_fixtures.py`, `tests/surface_*`, `tests/parser_library_test.py`,
  `tests/parser_binding_test.py`.

## Progress log

- 2026-10-21: the task file, with the amendments of ADR 0016 D2 and ADR 0017 D2 and D6.
- 2026-10-21: review of the task file: the program also gives the commands that the query
  diagnostic reads and the parser's resource limit, and the S1 report will say where its
  commands run. The second review had no findings.
- 2026-10-21: baseline: `nix-build integrity/judge.nix -A predictions --check` rebuilds the
  predictions in 30 s.
- 2026-10-21: the text package `packages/belay-sqlite-text` (`belaySqliteText`, Nix
  `textPackage`) holds the binding and the translation, moved from the surface with their module
  names. The binding takes the SQL as a `ByteArray`. The surface requires the text package and
  keeps `Belay`, `Belay.Sqlite` and `ParseCommand`; the surface build replays the text package and
  compiles only its own modules. The layer test checks the rules of the amended D2 for both
  packages. The surface suite (12 tests), the layer test and the Nix identity tests pass.
