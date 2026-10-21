# Status: one SQL translation, the text package below the surface

Created 2026-10-21. Status: OPEN.
Task: [task file](20261021-sql-text-package.task.md).
Specification: [ADR 0017](../docs/adr-0017-user-surface.md), D2 and D6;
[ADR 0016](../docs/adr-0016-model-and-surface.md), D2; all with their amendments of 2026-10-21.

## Relevant files

- The binding and the translation today: `packages/belay/Belay/Sqlite/{ParserLibrary,Parse,ParseTree,Grammar}.lean`,
  `packages/belay/Belay/Sqlite/Translation/`, `packages/belay/c/parser_shim.c`, `packages/belay/lakefile.lean`.
- The Python translation and binding: `belay/sqlite/syntax*.py`, `sql_tree.py`, `parser_library.py`, `located.py`.
- Callers: `migration_check/inputs.py`, `runtime.py`; `conformance/predict.py`, `generated_program.py`,
  `native_fixture.py`, `native_replay.py`, `native_trace.py`, `progress.py`, `record_parser.py`,
  `replay_tiers.py`, `restriction_examples.py`.
- Builds: `build-support/default.nix`, `runtime.nix`, `lean-package.nix`, `tests.nix`.
- Tests: `tests/syntax_*_test.py`, `tests/runtime_fixtures.py`, `tests/surface_*`, `tests/parser_library_test.py`,
  `tests/parser_binding_test.py`.

## Progress log

- 2026-10-21: the task file, with the amendments of ADR 0016 D2 and ADR 0017 D2 and D6.
- 2026-10-21: review of the task file: the program also gives the commands that the query
  diagnostic reads and the parser's resource limit, and the S1 report will say where its
  commands run. The second review had no findings.
