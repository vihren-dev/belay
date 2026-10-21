# One SQL translation: the text package below the surface (ADR 0017, D2)

Created 2026-10-21. Status: OPEN.
Status file: [status](20261021-sql-text-package.status.md).
Specification: [ADR 0017](../docs/adr-0017-user-surface.md), D2 and D6, with their amendments of
2026-10-21; [ADR 0016](../docs/adr-0016-model-and-surface.md), D2 and its amendment of 2026-10-21.
Depends on: [S1](20261021-surface-s1.task.md), where the owner chose candidate A, and
[the removal of the verifier product](20261021-remove-verifier-product.task.md) (ADR 0020).
Amended 2026-10-21 (ADR 0020): the CLI, the installed runtime and the kernel gate are gone, so the
program serves the harness only, and `located.py`'s path lookup, which only the CLI used, goes.

## Scope

The owner chose candidate A, the Lean port of the translation. This task makes the port the only
translation: the conformance harness and the elaborator both use it, and Python no longer loads
the parser library. The port and the parser binding move out of the surface into a package below
it, because the conformance runtime needs them and must not contain the surface (ADR 0016, D2,
amended).

Out of scope: the elaborators of S2 and later slices; installing the surface for Lean users (ADR 0016,
"Deferred"); a conformance runner that reads SQL text itself, so that no JSON of the syntax remains
between the harness and the runner.

## Outcome

1. **The text package.** A Lake package `belaySqliteText` in `packages/belay-sqlite-text`, with its
   own Nix derivation. It holds the C shim, the parser binding (`Belay.Sqlite.ParserLibrary`,
   `Parse`, `ParseTree`, `Grammar`) and the translation (`Belay.Sqlite.Translation` and its
   modules), with their module names kept. It requires only the model, and imports only the model's
   roots, `Init`, `Std` and `Lean`.
2. **The binding takes bytes.** A parse takes the SQL text as bytes, as the C API does, so that
   a text that is not valid UTF-8 gets the same `INPUT_ERROR` at the same offset as today. The
   translation's ranges stay UTF-8 byte offsets.
3. **The surface requires the text package.** The surface keeps `Belay`, `Belay.Sqlite` and the
   parse command (`ParseCommand`), and imports the binding and the translation from the text
   package. Its parse command and its suite behave as before.
4. **The translation program.** An executable of the text package reads requests as JSON lines,
   each with an execution profile, a source name and the SQL bytes, and writes one JSON line for
   each request: the statements with what the harness reads of them today (each statement's
   value and its start offset), or the refusal with the status, the source name, the
   range and the message that `SqlError` has today, and whether it is the parser's resource
   limit (`ParserResourceLimit`), which `predict.py` classifies apart. For a text that parses,
   the line also gives the commands that the grammar found, even when the translation refuses
   the text: the information that `native_replay.without_trailing_queries` reads from the parse
   tree today (each command's top-level symbols, a PRAGMA's name, and the refusal of a wrapper
   such as EXPLAIN). It selects the profile's grammar from the library's metadata, as
   `select_grammar` does today, and it refuses a profile without a grammar. One process
   translates a whole batch.
5. **Python no longer loads the parser library.** The conformance tools that parse or translate (`predict.py`,
   `generated_program.py`, `native_fixture.py`, `native_replay.py`, `native_trace.py`,
   `progress.py`, `record_parser.py`, `replay_tiers.py`, `restriction_examples.py`) call the
   program. The parse-only checks of `native_fixture.py` and `native_replay.py` use its refusals.
   These are deleted, with every caller changed: `belay/sqlite/syntax*.py`, `sql_tree.py`,
   `parser_library.py`, and the parts of `located.py` that the harness no longer reads; candidate B (`experiments/surface-s1/candidate-b`, `translate_b.py`, its
   Nix build and its test); the Lean-against-Python equality test and its fixture. The checks of the
   C library (`tests/parser_library_test.py`, `parser_binding_test.py`) test it through the Lean
   binding, or through a binding of their own in `tests/`.
6. **The conformance runtime** contains the program and the parser library that it links. It does
   not contain the surface.
7. **The layer test follows the amended D2.** No package below the text package imports or
   requires it or the surface; the surface may import the text package; the text package imports
   only the model's roots and Lean's libraries; the conformance runtime names the text package but
   not the surface.

## Tests

- **The predictions do not change.** The predictions of every frozen corpus are byte-identical to
  the predictions before the task, end to end through `predict.py` and the program. This test also
  replaces the equality test of S1 as the guard of ADR 0017 D6: the harness now uses the
  translation that the elaborator uses, and the judge compares its results with native SQLite.
- **The translation's tests.** The behavior that the 47 tests in `tests/syntax_*_test.py` check
  stays checked, against the Lean translation: through the program (for example with the
  `parse_sql` fixture changed to call it) or as Lean tests in the text package.
- **The program.** A test sends a batch with valid SQL, a grammar error, a model refusal, text that
  is not valid UTF-8, a text over the parser's resource limit and an unknown profile, and checks
  each result line.
- **The query diagnostic.** The diagnostic of the corpus report (`conformance/corpus.py`) gives the
  same categories as before for every frozen corpus, including texts with trailing read-only
  PRAGMAs that the translation refuses, such as `PRAGMA table_info(t)`.
- **No Python binding.** A test checks that no production Python module (`belay/`,
  `conformance/`) loads the parser library.
- **The layers.** The surface suite with the layer test of outcome 7 passes.
- `just test-full`, `just test-nix` and `just test-scheduled` pass. The
  status file records the time to build the predictions before and after the task.

## Key points

- **Process start.** Each Lean process loads its shared libraries and initializes the model's
  modules before it translates. Run one program for a batch, not one for each text, as
  `predict.py` already runs one `conformance-runner --predict` for its batch.
- **Raw bytes.** The harness passes SQL as bytes (`.encode()`), and the C tokenizer refuses invalid
  UTF-8 with `INPUT_ERROR`. `ParserLibrary.parse` takes a `String` today, which cannot hold such
  bytes.
- **Refusal text is evidence.** Prediction reasons contain `str(error)` and the source name (for
  example `corpus-migration.sql`). The program must give the same text, or the predictions change.
- **Shared libraries.** The precompiled translation calls the model's compiled code, so the model's
  shared library loads first (`sharedRequires` in `build-support/lean-package.nix`). The program
  links the parser library by an absolute rpath into the Nix store.
- **`located.py`.** Its path lookup (`span(path)`) had one caller, the CLI's diagnostics. The
  harness reads each statement's value (`predict.py`, `profile_scope.py`) and its start
  (`predict.py`); its `Json` type alias has importers across `conformance/`.
- **The judge.** The judge lock covers the judge, the claims, the corpora and the oracle, not the
  subject. This task changes only the subject, so it needs no judge pull request unless a claim
  or a corpus changes.
- **The S1 report** (`experiments/surface-s1/README.md`) is the record of a measurement. Its
  commands need the Python translation and candidate B. The change that deletes them adds a line
  to the report: the commands run on the tree before this task, and this task deleted what they
  need.
