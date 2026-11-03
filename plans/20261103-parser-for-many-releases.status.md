# Status: a parser library for the SQLite releases of the last two years

Date: 2026-11-03. Status: OPEN.
Audience: the implementation team.
Task: [20261103-parser-for-many-releases.task.md](20261103-parser-for-many-releases.task.md).
Specification: [ADR 0029](../docs/adr-0029-parser-for-many-releases.md).

## Relevant files

- `parser/dialects.json`, `parser/dialect_table.py`, `parser/grammar_sources.py`,
  `parser/generate.py`, `parser/library_steps.py`, `parser/library_metadata.py`
- `parser/tokenizer.c`, `parser/library_tokenizer.c`, `parser/library_grammar.c`,
  `parser/library_prefix.h`, `parser/library.c`
- `build-support/parser-library.nix`, `build-support/sources.nix`, `build-support/tests.nix`
- `packages/belay-sqlite-text/lakefile.lean`, `packages/belay-sqlite-text/Belay/Sqlite/Grammar.lean`
- `tests/parser_inputs.py`, `tests/parser_library_inputs.py`, `tests/parser_generated_test.py`,
  `tests/nix_suites.json`, `tests/test_nix_test_targets.py`

## Progress

- 2026-11-03: ADR 0029 accepted with the owner decisions; task and status files written.
