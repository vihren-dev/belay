# S1 measurements: SQL text in Lean

The measurements of ADR 0017, D2, for the owner's choice of the translation candidate.
Task: [`plans/20261021-surface-s1.task.md`](../../plans/20261021-surface-s1.task.md).

Machine: Linux x86_64, Intel Xeon E3-1275 v6 at 3.80 GHz, 8 threads. Lean 4.34.1 (the
pinned toolchain). Date: 2026-10-21.

## The texts

`texts.py` writes the SQL texts of the 48 frozen corpora of `judge/claims.json`, as the replay
reads them, to `build/surface-s1/texts.jsonl`, and their grammar and SQL alone to `sql.jsonl`:
for each case, the schema SQL of its initial state and its migration SQL. That is
14,430 texts, 1,764,669 bytes, all with one grammar (SQLite 3.51.0 without grammar options).
For each text it also records the Python binding's parse time and the Python translation's
result: the statements with the source range of each node, or the refusal (2,781 texts are
refused: grammar errors, statements that the model does not describe, and parser limits).

```sh
python3 experiments/surface-s1/texts.py build/conformance build/surface-s1
```

## Prototype 1: the parser in the Lean process

The surface package `packages/belay` binds the parser library's C API (`ParserLibrary.lean`,
`c/parser_shim.c`) and gives the command `#sql_parse "SQL"` (`ParseCommand.lean`).

### It loads

| Platform | Result |
| --- | --- |
| Linux x86_64 | Loads in `lake build`, `lake lean FILE` and the editor's server (`lake serve`); the `surface` suite passes in Nix. |
| macOS | Not measured yet: this machine is Linux. CI's check job runs on `macos-14` for manual runs and on `main`; one manual run of the branch measures it. |

How it loads: Lake compiles the package's modules to shared libraries (`precompileModules`)
and links them with the parser library; for a file that imports `Belay`, Lake gives `lean` and
the server the C shim as a dynamic library and the package's library as a plugin
(`lake setup-file`). Two findings:

- Lake compiles C with hidden symbols, so the shim marks its two functions for export itself.
- `lake env lean FILE` does not load the plugin. `lean` then aborts at the first parser call
  with an uncaught exception ("Could not find native implementation of external declaration"),
  not with an error at a position.

### Parse time

Each of the 14,430 texts parsed once, with its grammar, and read into a tree with the same
checks (three runs each; the garbage collector of Python is off while it parses):

| Binding | Total | Median per text | Largest |
| --- | --- | --- | --- |
| Lean, while a file elaborates (`ParseTime.lean`) | 2.56 to 2.58 s | 110 µs | 13 ms |
| Python (`parse_time.py`, `belay/sqlite/sql_tree.py`) | 4.19 to 4.41 s | 185 to 189 µs | 19 ms |

The whole file `ParseTime.lean`, with Lean's start and the JSON reading of the texts, takes
3.1 s.

```sh
S=build/lk/packages/belay; M=build/lk/packages/belay-sqlite-model
LEAN_PATH=$S/.lake/build/lib/lean:$M/.lake/build/lib/lean build/conformance/lean/bin/lean \
  --load-dynlib=$S/.lake/build/lib/libbelayParserShim.so --plugin=$S/.lake/build/lib/libbelay_Belay.so \
  experiments/surface-s1/ParseTime.lean
python3 experiments/surface-s1/parse_time.py build/conformance
```

### The editor

`editor.py` is a language server client: it opens a file in `lake serve`, as the editor's Lean
extension does, and prints the diagnostics when the server has processed the file.

| File | Diagnostics | Time to process |
| --- | --- | --- |
| `tests/surface/Accepted.lean` | 6:0, information: "SQLite's grammar accepts 3 commands" | 0.73 s |
| `tests/surface/Rejected.lean` | 6:21, error at `FORM`: "SQLite's grammar rejects the SQL here; ..." | 0.72 s |
| `Accepted.lean`, parser library missing | 1:0, error at the import: "error loading library, libsqlite-verifier-parser.so: cannot open shared object file: No such file or directory" | 0.47 s |

With the library missing, the server elaborates nothing after the import, and the error names
the library but not what to do. A clearer message needs the surface to load the library itself
(for example with `dlopen`) instead of through the plugin's link.

## Prototype 2: the translation in the elaborator

Each candidate goes from SQL text to the model's statement syntax, with the source range of each
node as `belay/sqlite/located.py` keeps it, and has the same refusals as the Python translation.
The comparison takes each text of `texts.jsonl` and compares the candidate's result with the
Python translation's result: the statements with the value, the range and the located parts of
each node, or the refusal with its status, message and range.

### Candidate A: a Lean port of the Python translation

`packages/belay/Belay/Sqlite/Translation/` ports `belay/sqlite/syntax*.py`, `located.py` and the
refusals of `sql_tree.py`, one Lean file for each Python module or less, from the parse tree of
prototype 1. A node is a `Located` value: the model's syntax value, such as a `Syntax.Statement`
or a `Syntax.Expr`, and a tree of ranges (`Span`) in the shape of the model's path steps. No JSON
is between the parse tree and the model's syntax. The functions call each other through the
subqueries of a query, so the two that close the loop are `partial` (`Mappers.lean`); the subquery
list of a statement is the state of the translation's monad, where the Python translation keeps it
in a context variable.

The comparison (`tests/surface/TranslationEquality.lean`) decodes each Python statement with the
model's codec (`Belay.Sqlite.Model.Codec.SyntaxJson`) and compares it with the port's value, and
compares the Python ranges with the port's ranges. A check of the comparison: with each port range
one byte longer, 10,298 texts differ; with each port value replaced by `COMMIT`, 10,297 differ.

| Measurement | Result |
| --- | --- |
| Texts whose result equals the Python translation's | 14,430 of 14,430 (2,781 refusals, 28,179 statements) |
| Parse and translation of all texts, while a file elaborates | 3.0 s (the parse alone: 2.57 s) |
| Code that would exist twice: the port, beside the Python translation until it is replaced | 1,223 lines of Lean code (1,791 with documentation), beside 1,398 lines of Python code |

The code lines count no blank lines, comments or docstrings. The test
`tests/surface_translation_test.py` (the `surface` suite) runs the same comparison over the 1,686
texts of the 42 authored corpora in 3 s.

```sh
BELAY_TRANSLATION_TEXTS=build/surface-s1/texts.jsonl PATH=build/conformance/lean/bin:$PATH \
  lake -d build/lk/packages/belay lean tests/surface/TranslationEquality.lean
```

Three findings about the package layout:

- A Lake library whose root is `Belay` takes every module under `Belay` as its own, the model's
  modules too, so a surface file that imported the codec did not build. The surface's library
  now names its modules (`globs` in `packages/belay/lakefile.lean`).
- `lean` with `LEAN_PATH` looks for the modules under `Belay` only in the first folder that has
  a `Belay` folder, so it does not find the model's modules beside the surface's. Lake gives
  `lean` the file of each import (`lake lean`, `lake setup-file`); the tests write the same
  module setup and give it to `lean` with `--setup` (`tests/surface_support.py`).
- The port's precompiled modules call the model's compiled code, so Lake builds the model's
  shared library for the surface and loads it before the surface's for a file that imports
  `Belay`. The model's Nix package has its C files, so the surface's Nix build only compiles and
  links them, and keeps the library (`sharedRequires` in `build-support/lean-package.nix`); the
  other packages' builds do not change.

### Candidate B: the translation in C

`candidate-b/` ports the same Python modules to C, one C file for each one or two of them. It
writes the result as JSON: the model's transport of each statement, with the range and the
located parts of each node, in the form of the Python translation. A refusal ends the
translation with `longjmp`, where the Python translation raises an exception; all memory of one
translation is in one arena. The prototype is a library of its own, `belay_translate`
(`translate_b.h`), linked with the parser library: it calls the parse and reads the parse
document into nodes (`entry.c`), so that the parser library does not change. A real candidate B
would sit in the parser library and read the parser's nodes directly, without `entry.c`.

| Measurement | Result |
| --- | --- |
| Texts whose result equals the Python translation's (JSON with sorted keys, so `true` and `1` differ) | 14,430 of 14,430 (2,781 refusals) |
| Parse, translation and JSON decoding in Python (`ctypes`) of all texts | 2.1 s |
| Size of the translation | 1,519 lines of C code (`entry.c` and `translate_b.h` excluded) |
| Code that would exist twice: the JSON shape of the model's syntax, which the Lean codec also decodes | 193 lines name a constructor, a field or an enumeration value of the shape; every line of the translation builds that shape |

Its statements are the Python translation's, so they decode to `Syntax.Statement` as those of
candidate A do. The test `tests/surface_translation_test.py` (the `surface` suite) compares both
translations over the 1,686 texts of the authored corpora in less than 1 s; the suite builds the
library with the parser library (`candidateB` in `build-support/tests.nix`).

```sh
P=build/parser-library
cc -std=c99 -O1 -Wall -Wextra -fPIC -fvisibility=hidden -shared -I$P/include \
  experiments/surface-s1/candidate-b/*.c -L$P/lib -lsqlite-verifier-parser -Wl,-rpath,$P/lib \
  -o build/surface-s1/candidate-b/libtranslate-b.so
python3 experiments/surface-s1/translate_b.py build/surface-s1/candidate-b/libtranslate-b.so
```

## Summary for the choice

| | A: Lean port | B: C in the parser library |
| --- | --- | --- |
| Equal to the Python translation | 14,430 of 14,430 | 14,430 of 14,430 |
| Size | 1,223 lines of Lean code | 1,519 lines of C code |
| Knowledge held twice | The whole translation, beside the Python translation until that is replaced | The JSON shape of the model's syntax, beside the Lean codec, as long as both exist |
| Where a change to the model's syntax goes | Lean only: the port builds `Syntax.Statement` values, so the compiler checks each constructor | C and the Lean codec, in step |
| Failure handling | Lean exceptions in a state monad; two `partial` functions | `longjmp` and an arena; memory errors are possible in C |
| Where the code ships | The surface package. When it replaces the Python translation, the CLI and the harness need it too, so the installed runtime gets a Lean program that runs it | The parser library, which is part of the installed runtime; the CLI and the harness call it as they call the parser |

Both reach the acceptance bar. The macOS measurement of prototype 1 is still open.

The owner chose candidate A on 2026-10-21.
