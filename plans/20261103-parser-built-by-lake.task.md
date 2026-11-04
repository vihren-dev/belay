# Lake builds the parser library from committed C sources

Date: 2026-11-03. Status: DONE (2026-11-03).
Audience: the implementation team.
Specification: [ADR 0023](../docs/adr-0023-parser-built-by-lake.md), accepted by the owner on
2026-11-03, with its owner decisions 1 to 6.
Record: [status](20261103-parser-built-by-lake.status.md).
Source baseline: main `5cdbc536` and the ADR revision `f16d3fd9`.

This is supporting work with a present problem: the owner asked for a Lake build of the text
package and the surface that needs no Nix and no `BELAY_PARSER_LIBRARY` (ADR 0023, "The
problem", owner decision 1). It changes no model code, no prediction, no claim and no lock.

## Required behavior

When the task is done, all of these are true:

1. **Committed generated C (D1).** `parser/generated/` holds the C files that the last stage of
   `build-support/parser-library.nix` compiles and that a generator writes: one folder per
   grammar, named by the 16 hexadecimal digits of its symbol prefix, the two library files at
   the top, and a manifest with each grammar's prefix, the source folder of its release and the
   compile flags. `just parser-sources` builds them with Nix and writes them into the checkout.
2. **Lake compiles the parser (D2).** The text package's lakefile compiles the C units with
   `buildLeanO`, the flags of the manifest, `SQLITE_OS_OTHER=1`, `SQLITE_THREADSAFE=0` and
   `parser/c-headers/` as system headers, given by an absolute path. It reads the grammars from
   the manifest. The units and the shim go into one static `extern_lib` with a new name for
   what it holds (owner decision 4); Lake also makes its shared library. The lakefile reads no
   environment variable for the parser and adds no linker arguments, search paths or run-time
   search paths for it. `c/parser_shim.c` includes `parser/library.h` directly.
3. **Own C library declarations (D2).** `parser/c-headers/` declares only what the units use,
   with standard C signatures; `FILE` is incomplete; `struct tm` is complete; no file has the
   name of a header in the toolchain's `include/clang`. `parser/library_tokenizer.c` defines
   `sqlite3_os_init` and `sqlite3_os_end`. The compile gives no warnings.
4. **One copy of the C (D3).** `parserLibrary.library` and its sanitized build compile the
   committed files with the headers, options and manifest flags of D2, with Lean's `clang`
   (the sanitized build keeps its own compiler and adds its sanitizer flags). The Nix
   `include/` output goes; the shared library `libsqlite-verifier-parser` stays for the
   driver of the `parserLibrary` suite.
5. **The variable is gone (D4).** No file outside `reviews/`, `plans/` and dated history sets
   or reads `BELAY_PARSER_LIBRARY`. `shell.nix` sets `BELAY_DEV_SHELL=1` (owner decision 3),
   and the `justfile` recipe `_dev-shell-warning` and `tests/dev_loop_test.py` use it.
   `shell.nix` imports `build-support/lean-toolchain.nix` instead of all of
   `build-support/default.nix`, and `.envrc` no longer watches files only for the parser.
6. **Every file of the D4 list is updated**: the variable users, shell detection, the rename
   fallout, the source sets, the test runtimes, the two tests of a missing parser library and
   the `library` parameter of `tests/surface_support.py` (removed), `pkgs.patchelf` in the
   surface suites' tools if nothing else there uses it, the stale text (the `grammarAdvice`
   message and the `TranslationProgram.lean` message as D4 words them, with no ADR number),
   and the amendments of ADRs 0007, 0010, 0016 and 0020. The list is a starting point:
   search again for the old names (`BELAY_PARSER_LIBRARY`, `parserShim`, `belayParserShim`,
   `sqlite-verifier-parser.h`, `parserLibrary.library` in user text) and fix every current
   user.
7. **Judge unchanged.** `integrity/judge.lock.json` and `judge/claims.json` do not change.

## Tests

The test suite of this task is D5 of the ADR:

- The Nix builds of the text package, the surface and the conformance runtime pass with no
  `BELAY_PARSER_LIBRARY` in any environment, and the text package's Nix build runs Lake with
  a `PATH` that has no `cc`, `gcc` or `clang`.
- The generation check (D3) is its own small Nix suite: a new entry in `tests/nix_suites.json`
  and its limits in `build-support/tests.nix` (owner decision 6). It passes on the commit, and
  the status file records once that a change of one byte in a committed file makes it fail
  with that file's name.
- The `parserLibrary` suite passes on the library compiled from the committed files.
- In the Nix suite that has the Lake output of the text package and the surface (owner
  decision 6): a test reads `ldd` (Linux) or `otool -L` (macOS) of `belay-sqlite-translate`,
  `belay-sql-check` and the shared libraries of the text package and the surface, and finds
  no parser library; and a test lists the undefined symbols of each object compiled from the
  C of D1 and requires each symbol that no other object of the library defines to be in a
  committed list (the ten functions of fact 6), with a comment per function on why its
  declaration is safe.
- `just verdict` passes, and the pull request records that the predictions of all corpora
  claimed in `judge/claims.json` are byte-identical to those of trunk.
- `tests/dev_loop_test.py` (ADR 0020, D6) finds the shell by `BELAY_DEV_SHELL` and, on Linux
  under the `LEAN_CC` wrapper, builds from a clean `.lake` of the text package with no
  missing-header or implicit-declaration warning; the translation program starts; and
  `lake lean` of a file with `#eval Belay.Sqlite.ParserLibrary.metadata` prints the metadata.
- The changed unit tests (`tests/test_source_identity.py`, `tests/surface_support.py` users,
  `tests/sql_file_support.py` users, docs tests) pass.

Each new test's docstring names the code of this repository that it checks (CLAUDE.md,
"Testing"). The owner checks the build on macOS; do not run macOS CI.

## Points to watch

- **Lake replays the text package in other workspaces** (fact 8). `surfacePackage`,
  `surfaceRoot` and the layout of `installed_layout` must hold the parser files at the same
  relative paths, or Lake rebuilds or fails there. `lean-package.nix` gets a parameter for
  extra source paths, and the `environment` parameter goes. Check that the lakefile's path to
  `parser/` is relative to the package folder, so that a git require with `subDir` works too.
- **Source identity.** `build-support/sources.nix` and `tests/test_source_identity.py` must
  make a change under `parser/generated/` or `parser/c-headers/` a change of the text
  package's identity. That test is strict; extend its components, do not loosen it.
- **The rename touches load order.** `tests/surface_support.py` loads shared libraries by file
  name in a fixed order for Lake's module setup. The new library name goes in the same place.
- **The `LEAN_CC` wrapper** in `shell.nix` replaces Lean's compile flags on Linux (fact 12).
  The lakefile's `-isystem` must come through it unchanged. Change the wrapper only if the
  local-loop test shows that it must.
- **Byte-identical output.** The generated files must equal what Nix generates today, and the
  manifest flags must equal those of `parser-library.nix`. Compare before you switch the Nix
  library to the committed files.
- **No compatibility paths** (CLAUDE.md, "Replaced code"): no fallback to the variable, no
  alias for the old target name.
- **Generated files and review.** The generated C is large; `just review` of the commit that
  adds it may need the reviewer to skip `parser/generated/`. Keep that commit free of other
  changes.

## Slices

1. Committed generated C, the manifest, `just parser-sources`, the generation check suite.
2. Lake compiles the parser; headers; rename; source sets; test runtimes; Nix library on the
   committed files; the variable and the two missing-library tests go; D5 link and symbol tests.
3. Shell and dev loop (`BELAY_DEV_SHELL`, `shell.nix`, `.envrc`, `justfile`), stale text and
   the ADR amendments.

Each slice ends with `just test-full` and `just verdict` after `just dev-build` passes. The
task ends with `just test-nix` and `just test-scheduled-checks`, once.
