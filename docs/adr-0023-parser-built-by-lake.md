# ADR 0023: Lake builds the parser library from committed C sources

Date: 2026-10-23. Status: PROPOSED.
Implementation: one task file and one pull request, after the owner accepts this ADR.
Audience: designers and reviewers.
Related: [ADR 0007](adr-0007-parser-library.md) (the parser library and its tests),
[ADR 0010](adr-0010-lake-builds-and-artifact-cache.md) (Lake builds, one Nix derivation per
Lean package), [ADR 0011](adr-0011-product-trust-and-development-integrity.md) (the judge's
subject), [ADR 0016](adr-0016-model-and-surface.md) ("Deferred": a separate repository for
the surface), [ADR 0017](adr-0017-user-surface.md) (D2: installing the surface with its native
library), [ADR 0020](adr-0020-local-build-loop.md) (the local build loop).

## Overview

The text package `packages/belay-sqlite-text` links the SQLite parser library, which only Nix
builds. Its lakefile reads the library's folder from the environment variable
`BELAY_PARSER_LIBRARY` and stops when the variable is not set. Thus every Lake build of the text
package or of the surface `belay` needs Nix and the variable: the Nix builds, the local loop,
the editor's server and each future user. This ADR makes Lake compile the parser library's C
code as part of the text package. Nix still generates the parser from the vendored SQLite
sources, and the generated C is committed. A Nix check makes sure that the committed C is what
the generation gives. After the change, a Lake build of the text package needs only the pinned
Lean and a C compiler named `cc`.

## Context

### The problem: only Nix can build the parser library

The owner asked on 2026-10-23 for the parser library to be built by Lake, as the first step of
an install path for Lean users. Today a user who requires the surface must:

1. install Nix and build `parserLibrary.library` from a checkout of this repository;
2. set `BELAY_PARSER_LIBRARY` to the result in each shell that runs Lake, and in the
   environment of the editor;
3. keep that Nix store path alive, because the text package's shared libraries and the
   translation program find the library through a run-time search path into the store.

The usual way for a Lean package with C code is an `extern_lib` that Lake compiles. A user then
needs only `lake build`.

### Facts that constrain the design

1. **Nix builds the library in three stages** (`build-support/parser-library.nix`). For each
   release: a check of the hashes of the vendored sources, then Lemon (compiled from the
   release's `lemon.c`) and `parser/library_steps.py`. For each grammar identity:
   `parser/generate.py` and Lemon generate the parser. Last, the C compiler compiles the
   objects and links one shared library. The two first stages need Python 3 and a compiled
   Lemon. Only the last stage is C compilation.
2. **The C that the last stage compiles.** For each grammar: `parser/library_tokenizer.c`,
   which includes the release's 9 MB `sqlite3.c`, and `parser/library_grammar.c`, with the
   generated `syntax.c`, `syntax.h`, `parse.h`, `token_map.inc` and `token_names.inc`. For the
   whole library: `parser/library.c` with the generated `library_grammars.inc` and
   `library_metadata.inc`. With the two grammars of today, the generated files are 708 KB.
   Each grammar adds about 330 KB.
3. **Lean's toolchain cannot compile this C on Linux.** Its `include/` folder has only
   `lean/` and the compiler's own headers in `clang/` (`stddef.h`, `stdint.h`, `float.h` and
   similar). It has no `stdio.h`. `parser/runtime.h` includes `stdio.h`, `stdlib.h` and
   `string.h`, and `sqlite3.c` includes more system headers. Lake's `buildO`, which compiles a
   C file that is not Lean output, calls `cc` by default (`Lake/Build/Common.lean` and
   `Lake/Build/Actions.lean` in Lean 4.34.1). `buildLeanO` uses Lean's own compiler and flags.
4. **The C compiles fast.** Measured on 2026-10-23 on one Linux x86_64 host (8 CPUs, load
   average 0.5), with GCC 15.3 and the flags of the Nix build (`-O1 -std=c99 -fPIC
   -fvisibility=hidden`): `library_tokenizer.c` for 3.51.0 in 0.62 s with 102 MB of memory,
   for 3.46.0 in 0.58 s, and `library_grammar.c` for 3.51.0 in 0.56 s. The tokenizer includes
   all of `sqlite3.c`, but the macros of `library_tokenizer.c` make SQLite's functions static,
   and the compiler drops what the tokenizer does not use.
5. **A trial build worked.** On 2026-10-23, in a copy of the model and text packages, the
   text package's lakefile was changed so that `buildO` compiles the five C units of fact 2 from
   the Nix-generated files. The units and the shim go into one static `extern_lib`. The
   `-L`, `-l` and run-time search path arguments were removed. With `BELAY_PARSER_LIBRARY` not
   set:
   - `lake build BelaySqliteText BelaySqliteText:shared parserShim:shared
     belay-sqlite-translate` passed (632 jobs, 42 s). From clean, the C part took 4 jobs and
     1.4 s.
   - The translation program links no parser library: `ldd` shows only glibc's libraries.
     Its shared library for the precompiled modules is 219 KB; the Nix-built parser library
     is 221 KB.
   - For all 11,118 distinct SQL texts of the parser's test inputs and of corpora v1 to v5
     (`parserLibrary.inputs`), under the three profiles 3.51.0, 3.46.0 and 3.53.4 (33,354
     requests), the trial program and the current program gave byte-identical answers.
     3.53.4 has no grammar, so both refuse those requests with the same message. The trial
     did not use the texts of the later corpora; the predictions test of D5 covers them.
   - `lake lean` of a file with `#eval Belay.Sqlite.ParserLibrary.metadata` printed the
     library's metadata. Elaboration called the parser through the precompiled modules.
6. **A Nix workspace holds only the package folders.** `sources.text` has the package folder
   as its root, and `build-support/lean-package.nix` copies it to its path in a copy of the
   repository layout, with the outputs of the required packages at their paths. The output of
   a package is its folder only. The surface's build replays the text package's output in its
   own workspace, and Lake checks the inputs of each target that it replays. Files outside
   the package folders, such as `parser/`, are in no workspace unless a derivation copies
   them there.
7. **Other users of the parser library.** The `parserLibrary` suite of `tests.nix` loads the
   Nix-built shared library: the comparison of each grammar with the corpora, the sanitizer
   job on Linux, the load test and the export check. `tests/surface_parser_test.py` checks
   the error when the shared library is missing. `shell.nix` sets `BELAY_PARSER_LIBRARY`, and
   the recipes and the test of the local loop use it to find out whether the shell is loaded
   (ADR 0020, D4 and D6).

## Decision

### D1. The generated C is committed under `parser/generated/`

The C files that the last stage compiles and that a generator writes (fact 2) are committed
under `parser/generated/`: one folder per grammar, named by the 16 hexadecimal digits of the
grammar's symbol prefix, and the two library files at the top of the folder. A manifest in the
same folder lists each grammar's prefix and the source folder of its release. The generation
stays in Nix, with its hash and identity checks, and does not change.

A recipe, `just parser-sources`, builds the generated files with Nix and writes them into the
checkout. A change to `parser/dialects.json`, to a vendored release or to a generator runs it,
and the change commits the result.

### D2. Lake compiles the parser library in the text package

The text package's lakefile compiles the C units of fact 2 with `buildO` and the system `cc`
(fact 3), with the flags of the Nix build. It reads the grammars from the manifest of D1, so a
new grammar changes no Lean code. The units and the shim go into one static `extern_lib`,
which Lake also makes as a shared library for the precompiled modules (fact 5). The lakefile
does not read `BELAY_PARSER_LIBRARY` and adds no linker arguments for the parser.

The text package refers to the C sources by their path in the repository: `parser/` for the
C files and the vendored releases, and `parser/generated/` for D1. Each Nix workspace that
builds or replays the text package has these files at the same paths (fact 6): the text
package's own build, the surface's build, and the build of any later package that requires
the text package. `lean-package.nix` gets a parameter for such extra source paths, and the
text package's dependents pass the same set. A git require with `subDir` gets the whole
repository, so the paths are there too.

The `extern_lib` gets a name for what it now holds, for example `parserLibrary`. The target
lists of the Nix build and of ADR 0020's D2 change with it.

### D3. One copy of the C for all builds

Nix's `parserLibrary.library` and its sanitized build compile the committed files of D1, not
the outputs of the generation. The `parserLibrary` suite then checks the C that Lake compiles
into the text package. A new Nix check compares the committed files with a fresh generation,
byte for byte, and names each file that differs.

The Nix build of the text package is the judge's subject (ADR 0011). Its translation program
now contains the parser that Lake compiled from the committed files. The check of this section
ties those files to the vendored sources and their hashes.

### D4. Nothing sets `BELAY_PARSER_LIBRARY`

The variable goes away from `build-support/default.nix`, `shell.nix`, the lakefiles, the
READMEs of `belay` and `belay-sqlite-text`, and the docstrings. The recipes and the test of
the local loop find out whether the shell is loaded from another variable that `shell.nix`
sets. The test of a missing parser library in `tests/surface_parser_test.py` goes, because no
separate library can be missing.

### D5. Tests

- **The Nix builds without the variable.** The text package, the surface and the conformance
  runtime build with no `BELAY_PARSER_LIBRARY` in any environment.
- **The generation check of D3.** It passes on the commit. A change of one byte in a committed
  file makes it fail with that file's name; the task records this once.
- **The `parserLibrary` suite** passes on the library compiled from the committed files.
- **No parser library at run time.** A test reads the dynamic dependencies of the translation
  program and of the text package's shared libraries (`ldd` or `otool -L`) and checks that
  none is a parser library. This tests our link configuration.
- **The same predictions.** `just verdict` passes. The pull request records that the
  predictions for all corpora are byte-identical to those of trunk.
- **The local loop.** The test of ADR 0020, D6, passes in the shell without the variable.

The owner checks the build on macOS.

## Consequences

- **A Lake build of the text package or the surface needs only the pinned Lean and `cc`.**
  On Linux, `cc` is the system compiler, for example GCC or Clang from the distribution. On
  macOS, it is the compiler of the Xcode command line tools. A clean build compiles the C in
  about 1.5 s (fact 5).
- **The editor needs no setup.** The editor's server loads the text package's shared
  libraries, which contain the parser.
- **The repository holds about 700 KB of generated C.** Each new SQLite release adds about
  330 KB. A diff of a grammar change shows the generated files too.
- **The conformance runtime no longer needs the parser library's store path at run time.**
- **Two builds compile the same C.** Nix compiles it for the `parserLibrary` suite and Lake
  compiles it for the text package. Both use the files of D1. The flags are in two places,
  in `parser-library.nix` and in the lakefile, and can drift apart.
- **The text package depends on the repository layout.** It reaches `parser/` with a relative
  path. A separate repository for the surface (ADR 0016, "Deferred") must bring these files.

## Alternatives considered

**Keep the Nix-built library and the variable.** Rejected. It is the problem: each Lake build
needs Nix, and each user needs a store path.

**Generate the parser in Lake.** Lake would compile Lemon and run `parser/generate.py` and
`parser/library_steps.py`. Rejected. Each user would need Python 3, and the generation would
run on the user's machine without the hash checks of Nix.

**Compile with Lean's own compiler (`buildLeanO`).** Rejected. Lean's toolchain has no C
library headers on Linux (fact 3).

**Download prebuilt libraries for each platform from a release.** Rejected for now. It needs a
release for each platform and run-time paths to the downloaded files, and the C compiles in
about 1.5 s. It can come back as a speed-up if the C becomes slow to compile.

**Move the C sources and the vendored releases into the text package.** Not chosen now. It
makes the package self-contained, but it moves 20 MB of vendored sources and changes the
paths in the generators, `parser/dialects.json`, the tests and the docs. A git require gets
the whole repository, so a present problem does not need it. The decision about a separate
repository (ADR 0016, "Deferred") decides it.

**Copy only the tokenizer code out of `sqlite3.c`.** Rejected. ADR 0007 uses SQLite's own
tokenizer from the release's `sqlite3.c`, and the grammar identity covers that code. A copy
would need its own check, and the compile time does not need it (fact 4).

## Not decided here

- The first release of the surface, its repository, its tags and a Reservoir entry (ADR 0016
  and ADR 0017, D2).
- A test in which a new project with only elan requires the surface by git and builds it. It
  comes with the release.
- User documentation for installing the surface.
- Platforms other than Linux x86_64 and macOS on Apple Silicon.

## Owner decisions

1. **This part comes before the first release.** ADR 0017, D2, keeps the install of the
   surface with its native library for the first release. This ADR takes the build of the
   native library out of that item, because the owner asked for it; the rest of the item stays.
   ADR 0017 gets an amendment that says so.
2. **The place of the C sources (D2).** Proposed: the text package reaches `parser/` by its
   path in the repository. The alternative moves them into the package (see "Alternatives
   considered").

## Sources

- Lake's C compile functions: `buildO`, `buildLeanO` and `compileO` in
  [`src/lake/Lake/Build/Common.lean`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Common.lean)
  and [`src/lake/Lake/Build/Actions.lean`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Actions.lean).
