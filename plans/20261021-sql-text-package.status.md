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
- 2026-10-21: review of the move: two must findings, fixed. `experiments/surface-s1/ParseTime.lean`
  passes bytes (it compiles and runs: 14,430 texts), and `tests/surface/InvalidUtf8.lean` checks
  that bytes that are not UTF-8 reach the library through the binding: a grammar error at offset 0,
  as the Python binding's test expects.
- 2026-10-21: the review of that fix had no findings.
- 2026-10-21: the translation program `belay-sqlite-translate` of the text package
  (`TranslationProgram.lean`, `Belay/Sqlite/TranslationRequest.lean`) and its test
  (`tests/translation_program_test.py`). A request has the profile's release, a source name and
  the SQL as hexadecimal bytes; the answer's `result` is `statements`, `translationRefusal`,
  `parseRefusal`, `limit`, `noParser` or `error`, and a parsed text also gives its commands.
  `selectGrammar` now takes the profile's compile options, as `select_grammar` does; the cases of
  `tests/test_dialect_selection.py` are `#guard`s in `tests/surface/GrammarChecks.lean`. The
  conformance runtime contains the program, and the layer test checks that its derivation names
  the text package; the model's roots come from the model's `lakefile.toml`, because the program
  imports the codec root `Belay.Sqlite.Model.Codec.SyntaxJson`. A scratch comparison over the
  27,151 texts of the frozen corpora (schema, migration and trace texts) gave the Python
  translation's answer for each, compared as JSON with sorted keys: values, ranges, refusals and
  commands. The program starts in about 30 ms; it links the model statically.
- 2026-10-21: review of the program: one should finding (R10), fixed: the answers for a request
  that is not usable and for an unusable parse document say what the caller can do.
- 2026-10-21: the review of that fix had no findings.
- 2026-10-22: the harness calls the program. `conformance/sql_text.py` keeps
  one program process for each process ID and runtime (`runtime_translator`); `TextParser` gives
  each text's `Translation`, whose `parsed()`, `statements()` and `commands()` raise the same
  `SqlError`s in the same order as before. `record_parser` and `default_parser` give a
  `TextParser`, and `predict.py`, `native_replay.py`, `native_trace.py`, `native_fixture.py`,
  `generated_program.py`, `restriction_examples.py`, `corpus.py`, `state_machine.py` and
  `measure_coverage.py` use it. `progress.py` and `replay_tiers.py` bind the program and the runner
  by digest, not the parser library. `ParserResourceLimit` and `NoParserForDialect` are in
  `belay/sqlite/errors.py`. The predictions of all frozen corpora are byte-identical to the
  baseline (`diff -r`), and they build in 30 s, as before. The conformance suites get
  `conformance/sql_text.py` with `record_parser.py` (`build-support/tests.nix`). `just build` first
  stopped at the resource guard (9.88 GiB free); the owner approved `nix-store --gc`, which freed
  3.2 GiB. `just test-source` (502 tests), `just test` (377 tests in 7 suites) and the model and
  frozen suites pass.
- To do in T4: the `parser-library` requirement of `requires_native` still checks the runtime's
  `lib`; rename it for the program when the C library tests move to the Lean binding.
- 2026-10-22: review of the switch: two should findings. R11 fixed: the client stops a program that
  gives no answer within 60 s, and a test checks it with a program that never answers. R10
  deferred: the Python `select_grammar` has no production caller, and T4 deletes it.
