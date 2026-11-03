# A parser library for the SQLite releases of the last two years

Date: 2026-11-03. Status: OPEN.
Audience: the implementation team.
Specification: [ADR 0029](../docs/adr-0029-parser-for-many-releases.md), accepted by the owner on
2026-11-03, with its owner decisions 1 to 3.
Record: [status](20261103-parser-for-many-releases.status.md).
Source baseline: `tasks/parser-built-by-lake` `d1f57d37` (pull request #304) and the ADR
revision of the bookmark `adr/0029-parser-for-many-releases`.

This is supporting work with a present problem: the owner asked for the parser and tokenizer
of every SQLite release of the last two years, as a test that the parser design scales, and
for a repository without vendored SQLite sources. It changes no model code, no prediction, no
claim and no lock.

## Required behavior

When the task is done, all of these are true:

1. **No SQLite source in the repository (D1).** `parser/upstream/` and
   `parser/upstream-3.46.0/` are gone. `parser/dialects.json` lists, for each release, its
   version, the year folder of its archives on sqlite.org and the SHA-256 of
   `sqlite-src-NNNNNNN.zip` and `sqlite-autoconf-NNNNNNN.tar.gz`.
   `build-support/parser-library.nix` fetches the archives with `fetchurl` and these hashes.
   The origin text of the old README is in `docs/sqlite-parser.md`.
2. **The cut tokenizer (D2).** For each tokenizer identity, `parser/generated/` has a folder
   with the cut of the release's `sqlite3.c`: the definitions that `parser/tokenizer.c` reaches,
   their types and macros and the release's token numbers, as unchanged text and in
   amalgamation order, taken by name. `parser/library_tokenizer.c` includes the cut instead of
   `sqlite3.c`, and nothing compiles `sqlite3.c` or `sqlite3.h` outside the generation.
3. **The slice check (D2)** is a step of the generation and fails it. For each tokenizer it
   compiles the cut and the full `sqlite3.c` with the wrapper at `-O0` and the other manifest
   flags, and requires the same machine code for each function of the cut object and of the
   wrapper, the same bytes for each table, and that the cut's symbols are all internal except
   the wrapper's.
4. **Identities and sharing (D3).** A parser identity, a tokenizer identity and a grammar
   identity of a dialect, as D3 defines them, with a new identity format name.
   `parser/generated/` has one folder per parser and one per tokenizer; the library has one
   grammar per distinct pair. The manifest names, for each grammar, its parser folder and its
   tokenizer folder, and no source folder.
5. **The releases (D4).** The dialect table lists 3.46.0 and the 23 releases of fact 1, each
   with the default grammar options, and records each dialect's grammar identity.
   `Release.default` stays 3.51.0. The metadata lists all 24 releases. `grammarAdvice` names
   no release; it names the releases that the library's metadata lists.
6. **No regular generation check (D5, owner decision 3).** The `parserSources` suite and
   `tests/parser_generated_test.py`'s comparison with a fresh generation are removed, with
   their entries in `tests/nix_suites.json`, `build-support/tests.nix`,
   `tests/test_nix_test_targets.py`, `docs/ci.md` and `build-support/README.md`. The manifest
   test moves to the `parserLibrary` suite. ADR 0023, D3, gets a dated amendment.
7. **Judge unchanged.** `integrity/judge.lock.json` and `judge/claims.json` do not change.

## Tests

The test suite of this task is D5 of the ADR:

- **The one generation.** `just parser-sources` passes with the slice check for every
  tokenizer; the status file records the Nix output of the generation and the slice check's
  output. The committed `parser/generated/` equals that output. The status file also records
  once that the slice check fails when a name is removed from the generator's list.
- **One case for each change of syntax.** `tests/parser_inputs.py` has a case for each change
  of facts 5 and 6 that changes what is accepted or how text is split into tokens, and a table
  of the release where each change came. The `parserLibrary` suite checks each case's status
  with each release's dialect: for example the `RAISE` case with an expression is rejected by
  3.46.0 and accepted from 3.47.1, and the trigger case with a schema name before the table is
  accepted from 3.52.0.
- **Every grammar parses every input**: the `parserLibrary` suite and its sanitizer job run
  with every grammar of the library.
- **The link and symbol tests of ADR 0023** pass for the new objects: no new undeclared C
  library call, and only the public API exported.
- `just verdict` passes, and the predictions of all claimed corpora are byte-identical to
  those of trunk.
- `tests/dev_loop_test.py` passes: the Lake build from a clean `.lake` compiles the new
  units without warnings.
- The changed unit tests (`tests/test_source_identity.py`, the dialect table and metadata
  tests, the `grammarAdvice` text) pass.

Each new test's docstring names the code of this repository that it checks (CLAUDE.md,
"Testing"). No test fetches an archive. The owner checks the build on macOS; do not run macOS
CI.

## Points to watch

- **The token names belong to the tokenizer.** `parser/tokenizer.c` includes
  `token_names.inc` (`case TK_X: return "X"`), which is a parser file today. A tokenizer
  object compiled once per tokenizer identity cannot depend on a parser file. Decide where the
  names live, and keep the parser identity's file list of D3 true to what the parser compiles.
- **Prefixes.** `parser/library_prefix.h` names every function by the grammar prefix. With
  shared objects, the tokenizer's wrapper functions need a prefix per tokenizer identity and
  the parser's per parser identity; `library_grammar.c` (the parse loop and the token map) is
  per pair.
- **The cut by name** must stay free of platform choices: no preprocessor run. The cut needs
  the macros and types of SQLite's internal headers that the reached definitions use
  (`u8`, `i64`, `SQLITE_DIGIT_SEPARATOR`, `sqlite3Isdigit`, `CC_*`, `TK_*`, `testcase`, ...).
  Release differences in these (facts 6) must not need per-release code in the generator.
- **The old identity code** (`grammar_sources.py`, `dialect_table.py`) digests text regions
  of `sqlite3.c` and the `-E` grammar. D3 replaces it; do not keep the old digest beside the
  new one (CLAUDE.md, "Replaced code"). The grammar options still come from the
  conditionals of `parse.y` and of the tokenizer sources.
- **The Lake build** (`packages/belay-sqlite-text/lakefile.lean`) reads `grammar.sources`
  from the manifest and depends on `sqlite3.c`; it must read the new folders instead.
  `build-support/sources.nix` and `tests/test_source_identity.py` must make every committed
  folder part of the text package's identity.
- **Archives in Nix.** The `sqlite-src` zip needs `unzip`. The autoconf archive of 3.51.0 and
  3.46.0 is the one `nix/sqlite.nix` already fetches; use the same hash.
- **Byte-identical predictions** need the 3.51.0 dialect's parse trees unchanged: its parser
  files may change only by prefix, and its tokenizer must behave as today.
- **No compatibility paths** for the old `sources` field or the upstream folders.
- **Generated files and review.** Keep the commit that adds generated C free of other
  changes, so that `just review` can be told to skip `parser/generated/`.

## Slices

1. Archives by hash and the cut tokenizer with its slice check, for today's two releases:
   new identities, new folders, Lake and Nix compile the cut, upstream folders removed,
   `parserSources` removed.
2. The 22 new releases in the dialect table, the generation, the syntax-change cases and
   `grammarAdvice` from the metadata.

Each slice ends with `just test-full` and `just verdict` after `just dev-build` passes. The
task ends with `just test-nix` and `just test-scheduled-checks`, once.
