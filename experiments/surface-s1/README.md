# S1 measurements: SQL text in Lean

The measurements of ADR 0017, D2, for the owner's choice of the translation candidate.
Task: [`plans/20261021-surface-s1.task.md`](../../plans/20261021-surface-s1.task.md).

Machine: Linux x86_64, Intel Xeon E3-1275 v6 at 3.80 GHz, 8 threads. Lean 4.34.1 (the
pinned toolchain). Date: 2026-10-21.

## The texts

`texts.py` writes the SQL texts of the 48 frozen corpora of `judge/claims.json`, as the replay
reads them: for each case, the schema SQL of its initial state and its migration SQL. That is
14,430 texts, 1,764,669 bytes, all with one grammar (SQLite 3.51.0 without grammar options).
For each text it also records the Python binding's parse time and the Python translation's
result: the statements with the source range of each node, or the refusal (2,781 texts are
refused: grammar errors, statements that the model does not describe, and parser limits).

```sh
python3 experiments/surface-s1/texts.py build/conformance build/surface-s1/texts.jsonl
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
