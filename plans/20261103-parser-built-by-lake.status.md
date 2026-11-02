# Lake builds the parser library: task status

Date: 2026-11-03. Status: OPEN.
Audience: the implementation team.
Task: [Lake builds the parser library](20261103-parser-built-by-lake.task.md).
Specification: [ADR 0023](../docs/adr-0023-parser-built-by-lake.md).
Source baseline: main `5cdbc536`.

Relevant files: `packages/belay-sqlite-text/lakefile.lean`, `packages/belay-sqlite-text/c/`,
`parser/`, `build-support/parser-library.nix`, `build-support/default.nix`,
`build-support/lean-package.nix`, `build-support/sources.nix`, `build-support/tests.nix`,
`shell.nix`, `.envrc`, `justfile`, `tests/surface_support.py`, `tests/sql_file_support.py`,
`tests/test_source_identity.py`, `tests/dev_loop_test.py`, `tests/nix_suites.json`.

## Progress

- 2026-11-03: task specified; ADR 0023 accepted by the owner.
