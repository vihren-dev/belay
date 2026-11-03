# Status: a parser library for the SQLite releases of the last two years

Date: 2026-11-03. Status: OPEN.
Audience: the implementation team.
Task: [20261103-parser-for-many-releases.task.md](20261103-parser-for-many-releases.task.md).
Specification: [ADR 0029](../docs/adr-0029-parser-for-many-releases.md).

## Relevant files

- `parser/dialects.json`, `parser/dialect_table.py`, `parser/grammar_sources.py`,
  `parser/generate.py`, `parser/library_steps.py`, `parser/library_metadata.py`
- `parser/tokenizer_cut.py`, `parser/slice_check.py`, `parser/release_step.py`
- `parser/tokenizer.c`, `parser/library_parser.c`, `parser/library_tokenizer.c`, `parser/library_grammar.c`,
  `parser/library_prefix.h`, `parser/library.c`
- `build-support/parser-library.nix`, `build-support/sources.nix`, `build-support/tests.nix`
- `packages/belay-sqlite-text/lakefile.lean`, `packages/belay-sqlite-text/Belay/Sqlite/Grammar.lean`
- `tests/parser_inputs.py`, `tests/parser_library_inputs.py`, `tests/test_tokenizer_cut.py`,
  `tests/test_parser_library_steps.py`,
  `tests/nix_suites.json`, `tests/test_nix_test_targets.py`

## Progress

- 2026-11-03: ADR 0029 accepted with the owner decisions; task and status files written.
- 2026-11-03, slice 1 (commit 601720b1): the generation fetches the archives of 3.46.0 and
  3.51.0 by hash, cuts each tokenizer and runs the slice check; `parser/generated/` has one
  folder per parser and per tokenizer identity; `parser/upstream*/` and the parserSources
  suite are removed. The new parsers equal the old ones apart from the symbol prefix.
  Tests run: `tests/test_tokenizer_cut.py`, `tests/test_parser_library_steps.py`,
  `tests/test_parser_library_build.py`, `tests/parser_build_test.py`,
  `tests/test_source_identity.py`, `tests/test_source_identity_derivations.py`,
  `tests/test_ci_scope.py`, `tests/docs_test.py`; `just dev-build`; Nix `tests.parserLibrary`.
- 2026-11-03, review of 601720b1: R11 must (no test of the slice check's comparator) rejected
  by decision 3 of ADR 0029, with the one manual negative check below; R10 should fixed (the
  Lake message for a missing folder says how to restore the tree).
- 2026-11-03, slice 2: `parser/dialects.json` has 24 releases (3.46.0, 3.47.1 to 3.54.1).
  `just parser-sources` gave 6 parsers, 8 tokenizers and 9 grammars, with the slice check
  passing for each release; output
  `/nix/store/777r9hvy7ym94n8ls1cgylc50m3y6nxr-sqlite-verifier-parser-generated` before the
  allocator change below; the committed tree is the output of the last run.
  - Lemon's template of 3.54.0 passes the parser context to `%realloc` and `%free`; the
    generated grammar now names macros of `parser/runtime.h` that take both forms, which
    changed every parser identity once more.
  - The production diff of the releases found more 3.52.0 syntax than ADR 0029 fact 5 named:
    five `ALTER TABLE` forms, and an alias (not a schema name) after a trigger's target
    table. Fact 5 and the task text are amended; `WITHIN GROUP` of 3.47.0 is only in
    `SQLITE_ENABLE_ORDERED_SET_AGGREGATES` builds.
  - Manual negative check, once, on 3.51.0: the slice check passes with the full name list
    (27 sections compared); without `sqlite3Isdigit` the cut does not compile; without
    `NDEBUG` it reports `.text.sqlite3ParserFallback` and `.text.keywordCode` as different.
  - Tests run: `tests/parser_inputs.py` cases through the Nix `tests.parserLibrary` (5 passed,
    with the sanitizers over all 9 grammars); `just dev-build`; the unit tests of slice 1 and
    `tests/test_parser_library_inputs.py`.
