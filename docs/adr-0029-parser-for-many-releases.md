# ADR 0029: A parser library for many SQLite releases

Date: 2026-11-03. Status: ACCEPTED (2026-11-03, owner decisions below).
Audience: designers and reviewers.
Related: [ADR 0007](adr-0007-parser-library.md) (the parser library: one library for all
grammars), [ADR 0023](adr-0023-parser-built-by-lake.md) (Lake compiles committed generated C),
[SQLite syntax boundary](sqlite-parser.md).

## Overview

The owner wants the parser to support many SQLite releases, and asked for the parser and
tokenizer of every release of the last two years as a test that the design scales. Today
the library has two releases (3.51.0 and 3.46.0). Each release adds about 10 MB of vendored
SQLite sources to `parser/`, because the tokenizer is compiled from the whole amalgamation
`sqlite3.c`. ADR 0023 compiles these sources with Lake, and its owner decision 2 moves them
into the repository that every Lean user clones.

This ADR keeps the parser's behavior: the exact grammar and tokenizer of each release. It
changes how the library gets and shares its C code:

- A generator cuts the tokenizer out of each release's `sqlite3.c`. The cut is committed with
  the generated parser, and a step of the generation proves that it compiles to the same
  machine code as the full amalgamation.
- Nix reads the SQLite sources from the official release archives by their hashes. The
  repository keeps the hashes, not the sources.
- A parser and a tokenizer each get an identity from what they compile, so releases share
  them when their compiled code is the same.
- The dialect table lists the 23 releases from 2024-11-03 to 2026-11-03 and keeps 3.46.0.

The model, the translation and the claims do not change. A release that this ADR adds is a
syntax that the parser recognizes, not a release whose semantics the model describes.

## Context

### Facts

The facts were measured on 2026-11-03, on the tree of pull request #304 (ADR 0023), with the
repository's own code (`parser/grammar_sources.py`, `parser/dialect_table.py`,
`parser/generate.py`) on the official archives of each release.

1. **The releases of the last two years.** The SQLite release history
   (<https://sqlite.org/chronology.html>) lists 23 releases from 2024-11-03 to 2026-11-03:
   3.47.1, 3.47.2, 3.48.0, 3.49.0, 3.49.1, 3.49.2, 3.50.0 to 3.50.4, 3.51.0 to 3.51.3,
   3.52.0, 3.53.0 to 3.53.4, 3.54.0 and 3.54.1. 3.51.3 (2026-03-13) came after 3.52.0
   (2026-03-06). 3.46.0 (2024-05-23) is older; the library has it today, and tests and
   conformance profiles use it.
2. **The vendored sources come from two archives per release.** `parser/upstream/README.md`
   names them: `parse.y`, `lemon.c` and `lempar.c` from `sqlite-src-NNNNNNN.zip` (about
   14.9 MB), and `sqlite3.c` and `sqlite3.h` from `sqlite-autoconf-NNNNNNN.tar.gz` (about
   3.3 MB). The autoconf archive is the one that `nix/sqlite.nix` already downloads for native
   SQLite, with the same SHA-256 (`42e26dfd…` for 3.51.0, `6f8e6a7b…` for 3.46.0). The
   vendored folders hold 10 MB (3.51.0) and 9.6 MB (3.46.0); `sqlite3.c` is 9.4 MB of each.
3. **The tokenizer uses a small part of `sqlite3.c`.** After the compile, each tokenizer
   object of the library defines only `sqlite3GetToken`, `keywordCode`, the keyword tables
   (`aKWHash`, `aKWNext`, `aKWLen`, `aKWOffset`, `aKWCode`, `zKWText`), the character class
   table `aiClass`, the tables `sqlite3CtypeMap` and `sqlite3UpperToLower` of `global.c`, and
   `yyFallback`, the fallback table of SQLite's own grammar, which the lookahead for
   `WINDOW`, `OVER` and `FILTER` reads. The other symbols of the 265,876 lines are unused.
4. **The grammar identity is finer than the parser.** The identity of `dialect_table.py`
   digests Lemon's `-E` output of `parse.y`, which contains SQLite's C actions. The generator
   replaces every action (`generate.py`), but patch releases change actions. Over the 26
   releases from 3.46.0 to 3.54.1:

   | What | Distinct |
   | --- | --- |
   | Grammar identities (today's digest) | 12 |
   | Lemon `-E` grammars | 11 |
   | Rewritten grammars (`syntax.y`) | 4 |
   | Generated parsers (`syntax.c` without paths) | 6 |
   | Tokenizer sources (the digested part of `sqlite3.c`) | 5 |
   | Token numberings (`token_map.inc`) | 3 |

5. **The generated parsers.** The six parsers are: 3.46.0 and 3.46.1; 3.47.0 to 3.48.0;
   3.49.0 to 3.49.2; 3.50.0 to 3.51.3; 3.52.0 to 3.53.4; 3.54.0 and 3.54.1. The grammar
   changes are: 3.47.0 accepts an expression as the second argument of `RAISE`; 3.49.0 adds
   the token `COMMENT`; 3.52.0 accepts a schema name before the table in the `INSERT`,
   `UPDATE` and `DELETE` of a trigger (`xfullname`, 409 to 412 productions). The template
   `lempar.c` changed in 3.50.0, 3.52.0 and 3.54.0, and so did the parser that Lemon writes.
6. **The tokenizers.** The tokenizer sources change in 3.49.0 (comments become `TK_COMMENT`),
   3.50.3 (the window lookahead skips comments), 3.51.0 (`sqlite3GetToken` returns `i64`) and
   3.52.0 (`keywordCode` takes and returns `i64`). The token numbers differ between 3.46 and
   3.47 while the tokenizer source does not, so a compiled tokenizer depends on its release's
   numbers too. With the numbers, there are six tokenizers; with the parsers, eight distinct
   pairs of parser and tokenizer.
7. **The repository assumes two releases in a few places.** `grammarAdvice` in
   `packages/belay-sqlite-text/Belay/Sqlite/Grammar.lean` names "3.51.0 or 3.46.0";
   `tests/parser_library_test.py` (`RAISE_ACCEPTED`) and `tests/test_parser_library_build.py`
   list the two releases; `build-support/sources.nix` and `parser-library.nix` read each
   release's folder. The grammar selection of `Grammar.lean` and the metadata of
   `parser/library.c` take any number of dialects.
8. **The generated C of one parser is about 280 KB** (`parser/generated/7c0495821ae35f29`).

## Decision

### D1. The release table names archives, and Nix fetches them

`parser/dialects.json` lists, for each release, its version, the year folder of its archives
on sqlite.org, and the SHA-256 of `sqlite-src-NNNNNNN.zip` and of
`sqlite-autoconf-NNNNNNN.tar.gz`. `build-support/parser-library.nix` fetches both archives
with `fetchurl` and these hashes, and takes `parse.y`, `lemon.c`, `lempar.c`, `sqlite3.c` and
`sqlite3.h` from them. The folders `parser/upstream/` and `parser/upstream-3.46.0/` go, with
their `sha256.json`; the archive hashes take their place. Their README text about the
origin of the files moves to `docs/sqlite-parser.md`.

Only the generation reads the archives: `just parser-sources`. The Lake build, the Nix library
and every test compile the committed files of D2, so no check run fetches an archive.

### D2. The tokenizer is cut out of `sqlite3.c` and committed

A generator step writes, for each tokenizer identity (D3), a C file with the parts of the
release's `sqlite3.c` that the tokenizer uses (fact 3), in their order in the amalgamation and
as unchanged text: the definitions that `parser/tokenizer.c` reaches, the types and macros that
they use, the token numbers of the release, and `yyFallback` with the function that reads
it. The generator takes these parts by name, with the file markers of the amalgamation
(`Begin file tokenize.c`), not by running the preprocessor, so the file has no platform's
choices in it. The list of names is part of the generator.

The **slice check** is a step of the generation, not a test suite: the generation fails when
it fails. It compiles, for each tokenizer, the cut file and the full `sqlite3.c` of its release
with the wrapper of `parser/tokenizer.c`, with the flags of the manifest but at `-O0`. It
requires that each function of the cut object, and each function of the wrapper, has the same
machine code as the function of the same name in the full object, and that each table has
the same bytes. At `-O0` the helpers that `-O1` inlines are functions of their own, such as
`getToken`, `analyzeWindowKeyword`, `analyzeOverKeyword`, `analyzeFilterKeyword` and
`sqlite3ParserFallback`, so the rule "each function of the cut object" compares them too, and
no list of names can miss one. The check compiles at `-O0` because at the
manifest's `-O1` the compiler inlines a static function that has one caller: `keywordCode`
has two callers in `sqlite3.c` and one in the cut, so its machine code would differ while its
text is the same. A release whose tokenizer needs a definition that the list does not name
fails this check or the compile, and the fix is a new name in the list.

`parser/library_tokenizer.c` includes the cut file in place of `sqlite3.c`. `sqlite3.h` is not
compiled; the cut file has the few declarations that it needs.

### D3. Identities by compiled code, and a dialect is a pair

- The **parser identity** is the SHA-256 of the generated parser files without paths
  (`syntax.c`, `syntax.h`, `token_names.inc`), generated with one fixed symbol prefix. The
  committed files are then generated again with the prefix of that identity
  (`Syntax_` and its first 16 hexadecimal digits), so that several parsers can be linked into
  one library. The fixed prefix keeps the identity free of itself.
- The **tokenizer identity** is the SHA-256 of the cut file of D2, which contains the token
  numbers. The cut file keeps SQLite's own linkage: its definitions are `static` or
  `SQLITE_PRIVATE` (which SQLite defines as `static` in the amalgamation), and
  `parser/library_tokenizer.c` defines `SQLITE_API` as `static` before it includes the file, as
  it does today for the whole `sqlite3.c`. So the symbols of two tokenizers do not collide;
  `parser/library_prefix.h` renames only the wrapper's functions. The slice check compares
  the objects' symbol tables too, so a cut that loses a `static` fails it.
- The **grammar identity** of a dialect, which the metadata and the Lean selection use, is the
  SHA-256 of the format name, its parser identity, its tokenizer identity and its grammar
  options. Its form for the Lean side does not change: one string for each dialect.

`parser/generated/` has one folder for each parser identity and one for each tokenizer
identity, and the library has one grammar for each distinct pair, with the token map of that
pair. Releases with the same pair share one grammar; releases with the same parser or
tokenizer share its compiled code. For the releases of D4 this gives six parsers, about six
tokenizers and eight grammars (facts 5 and 6; the cut of D2 adds `yyFallback`, so the
tokenizer count is the generator's to report).

`dialects.json` keeps the grammar identity of each dialect, and the generation fails when the
sources give another one, as today. The identity format name changes, so no old identity
matches a new one.

### D4. The releases

The dialect table lists the 23 releases of fact 1 and 3.46.0, each with the default grammar
options. `Release.default` stays 3.51.0. `grammarAdvice` reads the releases from the
metadata instead of naming them.

### D5. Tests

The generation runs once, with `just parser-sources`, and its result is committed (owner
decision 3). No check run generates again:

- **No generation check.** The `parserSources` suite of ADR 0023, which compares the committed
  files with a fresh generation, is removed; this amends ADR 0023, D3. Its manifest test, which
  reads only the committed files, moves to the `parserLibrary` suite.
- **The slice check of D2** runs once in the generation, for each tokenizer. The status file of
  the task records its output and the Nix output of the generation.
- **One case for each change of syntax.** `tests/parser_inputs.py` gets a case for each change
  of fact 5 and each change of fact 6 that changes what is accepted or how text is split into
  tokens. A table gives, for each release of the dialect table, the expected status of each
  case, and the `parserLibrary` suite checks it for every release. For example, the `RAISE`
  case is rejected by 3.46.0 and accepted from 3.47.1, and the trigger case with a schema
  name is accepted from 3.52.0. The table is derived from the release in which each change
  came, so a new release needs one line.
- **Every grammar parses every input.** The `parserLibrary` suite runs its inputs, and the
  sanitizer job, with every grammar of the library, as today for two.
- **The link and symbol tests of ADR 0023** cover the new objects; the cut tokenizers call
  no new C library function.
- **The predictions** of all claimed corpora are byte-identical to those of trunk, because the
  3.51.0 dialect parses with the same grammar and tokenizer code.

## Consequences

- The repository holds no SQLite source file. A release adds two hashes and one line in
  `dialects.json`, and generated C only when its parser or tokenizer is new: about 280 KB for
  a parser and much less for a tokenizer.
- The Lake build compiles about six parsers and six small tokenizers instead of two full
  amalgamations.
- The generation needs the archives: about 18 MB per release, 440 MB for the 24 releases,
  from the Nix store or from sqlite.org. Only `just parser-sources` fetches them; no check run
  needs them.
- The trust in the tokenizer moves from "the whole release file, hash-checked" to "a cut of
  it, which compiles to the same code as the whole file". The slice check of the one
  generation is the evidence.
- No check ties the committed generated C to the archives and the generators after the
  generation. A later change of a generator, or an edit of `parser/generated/`, is not found
  until the next `just parser-sources`. Such a check would not be a defense against tampering
  either (ADR 0011): its reference values are not in a protected file. The tests of D5 check
  what the committed C accepts.
- A user can select any release of the table for parsing. The model's semantics stay those
  of 3.51.0; the translation reports what it does not support, as today.
- The split of the surface into its own repository (ADR 0023, owner decision 2) moves the
  committed generated C only, not 10 MB per release.

## Alternatives considered

**Keep the whole `sqlite3.c` per release.** Rejected: about 9.4 MB per release in the
repository, and in the surface's repository after the split.

**A tokenizer cut by a C parser such as libclang.** Rejected for now: it finds the
definitions by itself, but it needs a new tool, and the preprocessor that it runs would put
platform choices into the cut. The list of names is short (fact 3), and the slice check finds
a missing name.

**Keep today's grammar identity.** Rejected: it gives 12 grammars where 8 compile differently
(fact 4), because it digests C actions that the generator removes.

**Only the latest patch of each minor release.** Rejected: the owner asked for all releases,
and patch releases do change parsers and tokenizers (3.46.1 action code, 3.50.3 tokenizer,
fact 6), which is the scaling that this ADR tests.

## Not decided here

- Semantics of the model for releases other than 3.51.0, and claims or corpora for them.
- Native SQLite builds of the new releases for conformance.
- Releases older than 3.46.0.

## Owner decisions

1. **The window.** DECIDED (a), 2026-11-03. Options: (a) the 23 releases from 2024-11-03 to 2026-11-03 and
   3.46.0, fixed in this ADR; (b) the same, and a rule that a new release joins the table when
   it appears; (c) only the latest patch of each minor release. Recommendation: (a). A rule
   for later releases needs a decision on who adds them and when, which the first public
   release can make.
2. **Native agreement of the new releases' parsers.** DECIDED (a), 2026-11-03: light tests
   only; the semantic model will test the parsers when it supports more releases, and this
   ADR's releases are a test of the design. Options: (a) the cases of D5
   only; (b) also a scheduled suite that compares each release's acceptance of the parser test
   inputs with native SQLite of that release (`sqlite3_prepare` on an empty database, syntax
   errors only), which needs a native build of each release. Option (b) uses native SQLite as
   an oracle for our code: the grammar rewrite of `parser/generate.py`, the token map and the
   tokenizer wrapper of `parser/tokenizer.c`. Recommendation: (a), because of the cost: 24
   native builds and a new scheduled suite. Our code is already checked by the production
   count of each generated parser against Lemon's export, by the cases of D5 for each release,
   and by the slice check; and today's library has no native comparison for its two
   releases either. If a case of D5 or a corpus finds a difference, (b) becomes the test for
   it.
3. **Where the generation check runs.** DECIDED (c), 2026-11-03: the generation runs once and
   its result is committed; a light check during that generation is allowed when it needs
   little code, and no check run generates again (D5). Options: (a) in every check run, as
   today; (b) only in the `full` CI scope and in the scheduled runs; (c) in no check run. A change under `parser/` selects
   `full` today (`tests/ci_scope.py`); a change of `build-support/parser-library.nix`, which
   writes the manifest and runs the generation, selects only `infrastructure`, so (b) adds
   that file to the files that select `full`. Recommendation: (b): the check fetches 440 MB of
   archives on a runner without a warm store, and only a change of the generation's inputs
   (`parser/`, `build-support/parser-library.nix`, the pinned toolchain) can make it fail.
   Before the decision the recommendation was (b).

## Sources

- SQLite release history: <https://sqlite.org/chronology.html>, read 2026-11-03.
- Release archives: `https://sqlite.org/YYYY/sqlite-src-NNNNNNN.zip` and
  `https://sqlite.org/YYYY/sqlite-autoconf-NNNNNNN.tar.gz`, for each release of fact 1.
