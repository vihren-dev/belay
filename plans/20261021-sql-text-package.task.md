# One SQL translation: the text package below the surface (ADR 0017, D2)

Created 2026-10-21. Status: OPEN.
Status file: [status](20261021-sql-text-package.status.md).
Specification: [ADR 0017](../docs/adr-0017-user-surface.md), D2 and D6, with their amendments of
2026-10-21; [ADR 0016](../docs/adr-0016-model-and-surface.md), D2 and its amendment of 2026-10-21.
Depends on: [S1](20261021-surface-s1.task.md), where the owner chose candidate A.

## Scope

The owner chose candidate A, the Lean port of the translation. This task makes the port the only
translation: the CLI, the conformance harness and the elaborator all use it, and Python no longer
loads the parser library. The port and the parser binding move out of the surface into a package
below it, because the installed runtime and the conformance runtime need them and must not contain
the surface (ADR 0016, D2, amended).

Out of scope: the elaborators of S2 and later slices; installing the surface for Lean users (ADR 0016,
"Deferred"); a resolver that reads SQL text itself, so that no JSON of the syntax remains between
the CLI and the gate.

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
   each request: the statements with their range trees, in the form that
   `belay/sqlite/located.py` reads today, or the refusal with the status, the source name, the
   range and the message that `SqlError` has today. It selects the profile's grammar from the
   library's metadata, as `select_grammar` does today, and it refuses a profile without a
   grammar. One process translates a whole batch.
5. **Python no longer loads the parser library.** The CLI (`migration_check/inputs.py`,
   `runtime.py`) and the conformance tools that parse or translate (`predict.py`,
   `generated_program.py`, `native_fixture.py`, `native_replay.py`, `native_trace.py`,
   `progress.py`, `record_parser.py`, `replay_tiers.py`, `restriction_examples.py`) call the
   program. The parse-only checks of `native_fixture.py` and `native_replay.py` use its refusals.
   These are deleted, with every caller changed: `belay/sqlite/syntax*.py`, `sql_tree.py` and
   `parser_library.py`; candidate B (`experiments/surface-s1/candidate-b`, `translate_b.py`, its
   Nix build and its test); the Lean-against-Python equality test and its fixture. The checks of the
   C library (`tests/parser_library_test.py`, `parser_binding_test.py`) test it through the Lean
   binding, or through a binding of their own in `tests/`.
6. **The runtimes.** The installed runtime and the conformance runtime contain the program and the
   parser library that it links. They do not contain the surface. The kernel gate contains
   neither, and its inputs stay the syntax JSON that it reads today.
7. **The layer test follows the amended D2.** No package below the text package imports or
   requires it or the surface; the surface may import the text package; the text package imports
   only the model's roots and Lean's libraries; the gate's derivations name neither package; the
   runtimes name the text package but not the surface.

## Tests

- **The predictions do not change.** The predictions of every frozen corpus are byte-identical to
  the predictions before the task, end to end through `predict.py` and the program. This test also
  replaces the equality test of S1 as the guard of ADR 0017 D6: the harness now uses the
  translation that the elaborator uses, and the judge compares its results with native SQLite.
- **The translation's tests.** The behavior that the 47 tests in `tests/syntax_*_test.py` check
  stays checked, against the Lean translation: through the program (for example with the
  `parse_sql` fixture changed to call it) or as Lean tests in the text package.
- **The program.** A test sends a batch with valid SQL, a grammar error, a model refusal, text that
  is not valid UTF-8 and an unknown profile, and checks each result line.
- **The CLI.** The runtime-package and installed-runtime tests pass, and the CLI's diagnostics of a
  grammar error, a refusal and invalid UTF-8 have the same messages and ranges as before.
- **No Python binding.** A test checks that no production Python module (`belay/`,
  `migration_check/`, `conformance/`) loads the parser library.
- **The layers.** The surface suite with the layer test of outcome 7 passes.
- `just test-full`, `just test-nix`, `just test-scheduled` and `just runtime-package` pass. The
  status file records the time to build the predictions before and after the task.

## Key points

- **Process start.** Each Lean process loads its shared libraries and initializes the model's
  modules before it translates. Run one program for a batch, not one for each text, as
  `predict.py` already runs one `conformance-runner --predict` for its batch.
- **The CLI's input.** The CLI reads up to 1 MiB of raw bytes, and invalid UTF-8 goes to the C
  tokenizer. `ParserLibrary.parse` takes a `String` today, which cannot hold such bytes.
- **Refusal text is evidence.** Prediction reasons contain `str(error)` and the source name (for
  example `corpus-migration.sql`). The program must give the same text, or the predictions change.
- **Shared libraries.** The precompiled translation calls the model's compiled code, so the model's
  shared library loads first (`sharedRequires` in `build-support/lean-package.nix`). The program
  links the parser library by an absolute rpath into the Nix store; the installer copies the Nix
  closure, so the path stays valid in the installed runtime.
- **`located.py` stays.** The CLI's diagnostics select a node's range by its path
  (`located[index].span(path)`); the program's output keeps that form.
- **The judge.** The judge lock covers the judge, the claims, the corpora and the oracle, not the
  subject. This task changes only the subject, so it needs no judge pull request unless a claim
  or a corpus changes.
- **The S1 report** (`experiments/surface-s1/README.md`) is the record of a measurement at its
  commit. It names that commit for its commands, and is not kept runnable after the Python
  translation is deleted.
