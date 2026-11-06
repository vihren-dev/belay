# ADR 0023: Lake builds the parser library from committed C sources

Date: 2026-10-23. Status: IMPLEMENTED in pull request #304, merged on 2026-11-04;
accepted by the owner on 2026-11-03. Revised 2026-11-02 to match the
repository of that day.
Implementation: one task file and one pull request:
[`plans/20261103-parser-built-by-lake.task.md`](../plans/20261103-parser-built-by-lake.task.md).
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
the generation gives. Lake compiles the C with the C compiler of Lean's toolchain and a small
set of C library headers that the repository holds. After the change, a Lake build of the text
package needs only the pinned Lean: no system C compiler and no Nix.

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
3. **Lean's toolchain has a C compiler but no C library headers.** The release archives of
   Lean 4.34.1 for Linux x86_64 and macOS aarch64 have `bin/clang`, a linker and `llvm-ar`.
   Their `include/` folder has only `lean/` and the compiler's own headers in `clang/`
   (`stddef.h`, `stdint.h`, `stdarg.h`, `float.h` and similar). There is no `stdio.h`. The
   libraries that Lean links into each program are in the archive: glibc in `lib/glibc` on
   Linux, `lib/libc/libSystem.tbd` on macOS. Lake's `buildO`, which compiles a C file that is
   not Lean output, calls `cc` by default. `buildLeanO` calls Lean's `clang` with Lean's flags,
   which include `-nostdinc` and the toolchain as the system root (`Lake/Build/Common.lean` and
   `Lake/Build/Actions.lean`). The Nix build of the repository uses the same release archives
   (`build-support/lean-toolchain.nix`). Where `LEAN_CC` is set, Lake does not use these
   flags (fact 12).
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
     (`parserLibrary.inputs`, which lists v1 to v5 on 2026-11-02 too), under the three profiles 3.51.0, 3.46.0 and 3.53.4 (33,354
     requests), the trial program and the current program gave byte-identical answers.
     3.53.4 has no grammar, so both refuse those requests with the same message. The trial
     did not use the texts of the later corpora. On 2026-11-02 main has 55 corpora (v1 to v55,
     `conformance/corpus-v*`), and `judge/claims.json` claims all of them and the synthetic
     workload. The trial is dated history. The predictions test of D5 covers all current
     corpora, and the implementation records its own result.
   - `lake lean` of a file with `#eval Belay.Sqlite.ParserLibrary.metadata` printed the
     library's metadata. Elaboration called the parser through the precompiled modules.
6. **The C needs few C library declarations.** With the SQLite options `SQLITE_OS_OTHER=1`
   (no operating system layer) and `SQLITE_THREADSAFE=0` (no mutexes), the five units include
   only these C library headers: `assert.h`, `ctype.h`, `math.h`, `stdio.h`, `stdlib.h`,
   `string.h` and `time.h`. Compiled at `-O1`, the objects call only ten C library functions:
   `calloc`, `fprintf`, `free`, `fwrite`, `malloc`, `memcpy`, `realloc`, `snprintf`, `strcmp`
   and `strlen`. The tokenizer objects call none. SQLite expects an application with
   `SQLITE_OS_OTHER` to define `sqlite3_os_init` and `sqlite3_os_end`. The compiler warns that
   they are not defined, and drops the code that calls them, because the tokenizer does not
   use it.
7. **A second trial compiled with Lean's compiler.** On 2026-10-23, the lakefile of fact 5 was
   changed to compile the units with `buildLeanO`, the two options of fact 6, and one folder of
   seven headers with 37 lines in total. The headers declare the C library functions that the
   units use, with their standard signatures. `FILE` is an incomplete type, and `struct tm` has a complete
   definition with the members that `sqlite3.c` uses. Lake ran with a `PATH` that had
   no `cc`, `gcc` or `clang`.
   - The build of fact 5 passed. From clean, the C part took 1.4 s (8 CPUs, load average 6.6).
   - For the 33,354 requests of fact 5, the answers were byte-identical to those of the
     current program.
   - The elaboration check of fact 5 passed.
8. **A Nix workspace holds only the package folders.** `sources.text` has the package folder
   as its root (`build-support/sources.nix`), and `build-support/lean-package.nix` copies it to
   its path in a copy of the repository layout, with the outputs of the required packages at
   their paths. The output of a package is its folder only. The surface's build replays the
   text package's output in its own workspace, and Lake checks the inputs of each target that
   it replays. Files outside the package folders, such as `parser/`, are in no workspace unless
   a derivation copies them there. On 2026-11-02 these workspaces build or replay the text
   package and so need the parser's C files at their paths:
   - `textPackage` in `build-support/default.nix`, which builds it;
   - `surfacePackage` in the same file, which requires and replays it;
   - the runtime root `surfaceRoot` of `build-support/tests.nix`, which the suites `surface`,
     `surfaceChecks` and `surfaceS6` use, and the copy of it that `installed_layout` in
     `tests/sql_file_support.py` makes for the Lake consumer of the SQL-file tests. Their
     `lake build` replays the packages that `surfaceRoot` links.
   These do not need the files, because they use finished outputs and run no Lake on the text
   package: `conformanceRuntime` (it copies the translation program), `theoremDependencies`
   (`build-support/theorem-dependencies.nix` links the outputs of `textPackage` and
   `surfacePackage` and runs `lean` on them), and `verifierConformance`,
   `conformanceCoverage`, `docTools`, the API reference (`api-reference.nix`,
   `api-reference-core.nix`), `public-documentation.nix` and `doc-gen4.nix`, which use the
   model package or no package of ours.
9. **Other users of the parser library.** On 2026-11-02 these read `BELAY_PARSER_LIBRARY` or
   depend on the Nix-built library, outside `reviews/` and `plans/`:
   - `build-support/default.nix` sets the variable for `textPackage` and `surfacePackage`
     (`environment.BELAY_PARSER_LIBRARY`).
   - `build-support/tests.nix` passes it to the surface suites
     (`environment.BELAY_PARSER_LIBRARY = surfacePackage.BELAY_PARSER_LIBRARY`, in
     `surfaceSuite`). `tests/sql_file_support.py` (`toolchain_environment`) gives it to the
     Lake process that builds the SQL-file consumer of `belay-sql-check`.
   - `shell.nix` sets it to `parserLibrary.library`. The recipe `_dev-shell-warning` of the
     `justfile` and `tests/dev_loop_test.py` use it to find out whether the shell is loaded
     (ADR 0020, D4 and D6).
   - The lakefile and README of `packages/belay-sqlite-text`, and the lakefile docstring and
     README of `packages/belay`, name it. `experiments/surface-s1/editor.py` names it in its
     docstring.
   The `parserLibrary` suite of `tests.nix` loads the Nix-built shared library: the comparison
   of each grammar with the corpora, the sanitizer job on Linux, the load test and the export
   check. Two tests check the error when the text package's shared library cannot find the
   parser library: `test_missing_parser_library_is_a_load_error` in
   `tests/surface_parser_test.py` and `test_missing_parser_library_is_not_an_expected_failure`
   in `tests/surface_sql_doc_blocks_test.py`.
10. **What other Lean packages do.** On 2026-10-23, the lakefiles of Lean packages with C code
    on GitHub showed three ways (see "Sources"):
    - Most compile vendored C with `buildO` or `compileO` and the system `cc`: `leansqlite`
      (the SQLite amalgamation), `nauty-ffi`, `CMark.lean` and `md4lean`, which doc-gen4
      requires. The README of `leansqlite` says that the build "requires a C compiler called
      `cc` on the `PATH`". Its lakefile disables SQLite's large file support because "Lean's
      bundled libc only provides fcntl and not fcntl64".
    - Some use Lean's `clang` with other headers. On Windows, `md4lean` adds its own
      `stdio.h`, `stdlib.h` and `string.h`. `lean-beam` removes `-nostdinc` and the system
      root from Lean's flags and uses the headers of the host, from `xcrun --show-sdk-path` on
      macOS.
    - `LeanCopilot` and `lean-egg` download prebuilt libraries from their GitHub releases
      (`preferReleaseBuild`), because their native parts need CMake or Cargo.

11. **Several programs and libraries contain the parser.** On 2026-11-02 the Lake targets that
    link the parser are the text package's `BelaySqliteText:shared`, `parserShim:shared` and
    `belay-sqlite-translate`, the surface's `Belay:shared`, which loads the text package's
    libraries, and the surface's executable `belay-sql-check` (ADR 0017, S7). The executable
    reaches the parser through the text package: it is built with `supportInterpreter := true`
    and the text package's `lean_lib` carries the link arguments. `conformanceRuntime` copies
    the translation program. The editor's server and the test processes load the shared
    libraries.
12. **The dev shell compiles with its own `LEAN_CC` on Linux.** `shell.nix` sets `LEAN_CC` to
    a script that wraps the toolchain's `clang` (ADR 0020, fact 4 and D1), because that clang
    links for a loader that NixOS does not have. In `Lake/Config/InstallPath.lean`, a set
    `LEAN_CC` makes Lake use that path as `cc` and not add the flags of the toolchain's
    internal compiler (`getInternalCFlags`: `ccFlags` is then only `cFlags`). Then
    `buildLeanO` in `Lake/Build/Common.lean` runs `LEAN_CC -c -o OBJECT SOURCE -I
    TOOLCHAIN/include CFLAGS WEAK-ARGS TRACE-ARGS`. The script looks for `-c` among its
    arguments. For a compile it runs `clang --sysroot TOOLCHAIN -nostdinc -isystem
    TOOLCHAIN/include/clang` and then all arguments of Lake. For a link it adds the linker
    flags. On macOS `LEAN_CC` is not set and Lake uses the toolchain's `clang` with its own
    flags. The script copies those flags (its comment says that a Lean upgrade can change
    them) and puts them before the arguments of Lake, so an `-isystem` that the lakefile passes
    is searched after the toolchain's compiler headers.

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

The text package's lakefile compiles the C units of fact 2 with `buildLeanO`, that is, with
Lean's `clang` and Lean's flags (fact 3). It adds the flags of the Nix build, the two options of
fact 6, and the headers of `parser/c-headers/` as the system headers. It reads the grammars from
the manifest of D1, so a new grammar changes no Lean code.

`parser/c-headers/` declares only what the five units use (fact 6). Each function has its
standard C signature, because the linker resolves it in the C library that Lean links (fact
3), and a wrong declaration compiles and links without an error. A type that the source uses
only through pointers, such as `FILE`, stays incomplete. A type whose members the source uses,
such as `struct tm` in `sqlite3.c`'s date functions, gets a complete definition, because the
compiler checks the source before it drops unused code. Its layout can differ from the C
library's, because no kept code calls a C library function with it; the symbol test of D5
makes sure of that. `parser/library_tokenizer.c` defines `sqlite3_os_init` and
`sqlite3_os_end` as functions that return `SQLITE_OK` (fact 6), so that the compile gives no
warnings. A new SQLite release that needs more declarations adds them here, and the symbol
test of D5 shows which functions it calls.

Under the wrapper of fact 12, the same compile behaves as follows. Lake passes `-c`, so the
script adds `--sysroot` and `-nostdinc` itself, and Lake's own arguments follow: the `-I` of
Lean's include folder, the flags of the Nix build, the two options of fact 6 and `-isystem` with
the path of `parser/c-headers/`. Thus a unit sees the same header search list as in the
unwrapped compile: the folders of `-I` first (Lean's include folder, which has `lean/` and
`clang/` and no C library header), then the `-isystem` folders in order (the compiler's headers
of the toolchain, then `parser/c-headers/`), and no host header. A file in `parser/c-headers/`
must not have the name of a header in the toolchain's `include/clang`, because that header is
found first in both compiles. The
lakefile gives the path as an absolute path, because it must not depend on the folder in
which Lake runs the compiler. The script does not read the other arguments, so the compile
needs no change of it. If a Lean upgrade changes the toolchain's flags, the script and this
compile change together, and the local-loop test of D5 shows it.

The units and the shim go into one static `extern_lib`, which Lake also makes as a shared
library for the precompiled modules (fact 5). The lakefile does not read
`BELAY_PARSER_LIBRARY` and adds no linker arguments for the parser.

The text package refers to the C sources by their path in the repository: `parser/` for the
C files and the vendored releases, and `parser/generated/` for D1. Each Nix workspace that
builds or replays the text package has these files at the same paths (fact 8): `textPackage`,
`surfacePackage`, the runtime root `surfaceRoot` of `build-support/tests.nix` with the layout
that `tests/sql_file_support.py` copies from it, and the build of any later package that
requires the text package. `theoremDependencies`, `conformanceRuntime` and the documentation
builds use finished outputs or other packages, and need nothing. `lean-package.nix` gets a parameter for such extra source paths, and the
text package's dependents pass the same set. A git require with `subDir` gets the whole
repository, so the paths are there too.

The `extern_lib` is renamed from `parserShim` (static library `belayParserShim`) to a name for
what it now holds, for example `parserLibrary` (owner decision 4). The rename is in the same
pull request, and D4 lists the places that name the old one. `c/parser_shim.c` includes
`parser/library.h` directly, so the Nix `include/` output of the parser library is not needed
and goes. The Nix-built shared library `libsqlite-verifier-parser` stays, for the driver of the
`parserLibrary` suite.

### D3. One copy of the C for all builds

Nix's `parserLibrary.library` and its sanitized build compile the committed files of D1, not
the outputs of the generation. They use the headers and the options of D2. The library uses
Lean's `clang` from the pinned toolchain, as Lake does. The sanitized build keeps its own
compiler and adds its sanitizer flags. The manifest of D1 holds the compile flags, and the
lakefile and `parser-library.nix` read them from it. The `parserLibrary` suite then checks the
C that Lake compiles into the text package, as Lake compiles it. The sanitizer flags stay in Nix only. A new Nix check compares the committed files with a
fresh generation, byte for byte, and names each file that differs. It is a small suite of its
own (owner decision 6): a new entry in `tests/nix_suites.json` and its limits in
`build-support/tests.nix`.

The Nix build of the text package is the judge's subject (ADR 0011). Its translation program
now contains the parser that Lake compiled from the committed files. The check of this section
ties those files to the vendored sources and their hashes.

Amendment, 2026-11-03 ([ADR 0029](adr-0029-parser-for-many-releases.md), D5 and owner
decision 3): the check that compares the committed files with a fresh generation, the
`parserSources` suite, is removed. The generation runs once, with `just parser-sources`, from
the official release archives, and its result is committed; no check run generates again. The
manifest test of that suite is now in the `parserLibrary` suite.

### D4. Nothing sets `BELAY_PARSER_LIBRARY`, and the files that change with it

The variable goes away, and the dev shell is found by another variable: `shell.nix` sets
`BELAY_DEV_SHELL=1` (owner decision 3), because macOS has no `LEAN_CC` to test. This is the
list of the files that the change touches, as checked on 2026-11-02. The implementation takes
it as a starting point and searches again.

- **The variable (fact 9).** `build-support/default.nix`, `build-support/tests.nix`
  (`surfaceSuite`), `tests/sql_file_support.py` (`toolchain_environment`), `shell.nix`, the
  lakefile and README of the text package, the README and the lakefile docstring of `belay`,
  `experiments/surface-s1/editor.py`. The `environment` parameter of
  `build-support/lean-package.nix` has no other user, so it goes; the parameter for extra
  source paths (D2) takes its place.
- **Shell detection.** The `justfile` recipe `_dev-shell-warning`, `tests/dev_loop_test.py`
  and ADR 0020, D6 use `BELAY_DEV_SHELL`.
- **The rename of the `extern_lib` (D2).** The target lists in the `justfile` (`dev-build`)
  and `build-support/default.nix` (`textPackage`); `tests/surface_support.py`, which loads
  `libbelayParserShim` by its file name; the target table of ADR 0020, D2.
- **Source sets.** `build-support/sources.nix` (`text` names `c/parser_shim.c` only; it gains
  the committed C, the headers and the manifest through the extra source paths) and
  `tests/test_source_identity.py` (`PARSER_LIBRARY_INPUTS` and the components of the text
  package: a change under `parser/generated/` changes the identity of the text package).
- **Test runtimes (fact 8).** `surfaceRoot` in `build-support/tests.nix` and
  `installed_layout` in `tests/sql_file_support.py` get the parser files. The lakefile reaches
  `parser/` by a path relative to the package folder; the implementation checks that this
  also works for a git require with `subDir`.
- **Tests that go.** The two tests of a missing parser library (fact 9), the `library`
  parameter of `module_setup` and `surface_command` in `tests/surface_support.py`, and
  `pkgs.patchelf` in the tools of the surface suites if nothing else there uses it.
- **Stale text.** The message `grammarAdvice` in
  `packages/belay-sqlite-text/Belay/Sqlite/Grammar.lean` tells the user to rebuild the parser
  library; it says instead that a new dialect goes into `parser/dialects.json` and
  `just parser-sources`, and names no ADR. The message of an unusable parse document in
  `packages/belay-sqlite-text/TranslationProgram.lean` tells the user to rebuild the conformance
  runtime with Nix; it says instead to rebuild the translation program with Lake.
  The comments and documents that say that Nix builds
  the parser library or that the program links it by a store path change too:
  `conformance/progress.py`, the comment of `textPackage` in `build-support/default.nix`,
  `build-support/README.md`, `docs/sqlite-parser.md`, `docs/ci.md` (it also lists the suite
  of D3), the comment of the `justfile` recipe that builds the conformance runtime, and
  `sqlite-migration-verifier-team-guide.md`.
- **The shell.** `shell.nix` imports `build-support/lean-toolchain.nix` and not all of
  `build-support/default.nix`, because it no longer needs the parser library. `.envrc` stops
  watching `parser` and `build-support/*.nix` for it, and its comment changes.
- **Amendments of ADRs, as work of the implementation.** ADR 0007 (a Lake build compiles the
  library into the text package; the Nix shared library stays for the Nix suite), ADR 0010
  (extra source paths; a Lake build needs no Nix), ADR 0016 (the text on the program that
  links the library, and "Deferred" with owner decision 2), ADR 0020 (fact 5, D1, D2's target
  table and D6). ADR 0017, D2, is amended with this revision.
- **The judge.** `integrity/judge.lock.json` and `judge/claims.json` do not change. The
  byte-identical predictions of D5 are the evidence that the behavior is the same.

### D5. Tests

- **The Nix builds without the variable.** The text package, the surface and the conformance
  runtime build with no `BELAY_PARSER_LIBRARY` in any environment.
- **The generation check of D3**, in its own small Nix suite. It passes on the commit. A
  change of one byte in a committed file makes it fail with that file's name; the task records
  this once.
- **The `parserLibrary` suite** passes on the library compiled from the committed files.
- **No parser library at run time.** A test, in the Nix suite that has the Lake output of the
  text package and the surface (owner decision 6), reads the dynamic dependencies (`ldd` or
  `otool -L`) of every program and shared library that contains the parser (fact 11):
  `belay-sqlite-translate`, `belay-sql-check`, and the shared libraries of the text package and
  of the surface. It checks that none is a parser library. The change that adds a program
  or shared library with the parser adds it to this list. This tests our link configuration.
- **The C library functions.** A test, in the same suite, lists the undefined symbols of each object that the
  text package compiles from the C of D1. Each symbol that is not defined by another object of
  the library must be in a committed list: the ten functions of fact 6. The list has a comment
  that says why each function is safe to declare in `parser/c-headers/`. This tests our headers:
  a new function in the list needs a review of its declaration.
- **No system C compiler.** The Nix build of the text package runs Lake with a `PATH` that has
  no `cc`, `gcc` or `clang`.
- **The same predictions.** `just verdict` passes. The pull request records that the
  predictions for all corpora claimed in `judge/claims.json` (55 corpora and the synthetic
  workload on 2026-11-02, not only the v1 to v5 of the trial in fact 5) are byte-identical to
  those of trunk.
- **The local loop under the `LEAN_CC` wrapper.** The test of ADR 0020, D6
  (`tests/dev_loop_test.py`), passes in the shell of `shell.nix`, which it finds by `BELAY_DEV_SHELL`, on
  Linux with the wrapper of fact 12. It runs `just dev-build` from a clean `.lake` of the text
  package, so that Lake compiles the C units through the wrapper with `-isystem
  parser/c-headers`, and it checks that the compile gives no warning about a missing header
  or an implicit declaration, that the translation program starts, and that `lake lean` of a
  file with `#eval Belay.Sqlite.ParserLibrary.metadata` prints the metadata (the check of
  fact 5). The symbol test above also runs on these objects. The owner runs the same on
  macOS, where no wrapper is set.

The owner checks the build on macOS.

## Consequences

- **A Lake build of the text package or the surface needs only the pinned Lean.** It needs
  no system C compiler, no C library headers and no Xcode command line tools. A clean build
  compiles the C in about 1.5 s (facts 5 and 7). Most Lean packages with C code need `cc`
  (fact 10); this one does not.
- **The repository maintains its own C library declarations.** They are few (fact 6), and the
  test of D5 shows each new function that a new SQLite release calls.
- **The parser runs with `SQLITE_OS_OTHER` and `SQLITE_THREADSAFE=0`.** The tokenizer does not
  use the operating system layer or the mutexes. The `parserLibrary` suite and the predictions
  test check the parser with these options.
- **The editor needs no setup.** The editor's server loads the text package's shared
  libraries, which contain the parser.
- **The repository holds about 700 KB of generated C.** Each new SQLite release adds about
  330 KB. A diff of a grammar change shows the generated files too.
- **The conformance runtime no longer needs the parser library's store path at run time.**
- **Two builds compile the same C.** Nix compiles it for the `parserLibrary` suite and Lake
  compiles it for the text package. Both use the files, the headers and the flags of D1 and
  D2, with the same compiler.
- **The text package depends on the repository layout.** It reaches `parser/` with a relative
  path. A separate repository for the surface (ADR 0016, "Deferred") must bring these files
  (owner decision 2).

## Alternatives considered

**Keep the Nix-built library and the variable.** Rejected. It is the problem: each Lake build
needs Nix, and each user needs a store path.

**Generate the parser in Lake.** Lake would compile Lemon and run `parser/generate.py` and
`parser/library_steps.py`. Rejected. Each user would need Python 3, and the generation would
run on the user's machine without the hash checks of Nix.

**Compile with the system `cc` (`buildO`).** This was the first proposal, and most Lean packages
do it (fact 10). Rejected. Many machines have no C compiler, for example a macOS machine
without the Xcode command line tools, and the build then fails for a reason that the user cannot
see in Lean. The first trial (fact 5) shows that it works where `cc` exists.

**Compile with Lean's `clang` and the host's headers, as `lean-beam` does.** Rejected. It still
needs the C library headers of the host, from a development package or the Xcode command line
tools.

**Download prebuilt libraries for each platform from a release (`preferReleaseBuild`).**
Rejected for now. It needs a release for each platform, and Lake must still build from
source where no archive matches. The packages that do it need tools that a user does not have
(fact 10); this build needs none, and the C compiles in about 1.5 s. It can come back as a
speed-up if the C becomes slow to compile.

**Move the C sources and the vendored releases into the text package now.** Not chosen. It
makes the package self-contained, but it moves 20 MB of vendored sources and changes the
paths in the generators, `parser/dialects.json`, the tests and the docs. A git require gets
the whole repository, so a present problem does not need it. Owner decision 2 moves the
files at the split of the repository.

**A separate repository for the parser.** Rejected. A grammar change changes the generated C,
the grammar identity, the translation in the text package, the predictions and the corpora in
one change. With two repositories, each such change is two pull requests and a pinned revision,
and the checks of D3 must fetch the other repository. Only the text package and our tests use
the C library.

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
- Follow-ups, separate from this change: the history notes in the README of
  `experiments/surface-s1`, and the move of the C into the text package at the split of the
  repository (owner decision 2).

## Owner decisions

1. **This part comes before the first release.** DECIDED by the owner on 2026-11-02: Lake
   builds the parser library before the first release of the surface. ADR 0017, D2, kept the
   install of the surface with its native library for the first release. This ADR takes the
   build of the native library out of that item; the rest of the item stays. ADR 0017, D2,
   has an amendment of 2026-11-02 that says so.
2. **The place of the C sources (D2).** Decided by the owner on 2026-10-23:
   - Until the first release, the C sources stay in `parser/` in this repository, and the
     text package reaches them by their path.
   - At the split of the surface into its own repository (ADR 0016, "Deferred"), the files
     that Lake compiles move into the text package in that repository: the generated C of D1,
     `parser/c-headers/`, the C files of `parser/`, and each release's `sqlite3.c` (about 9 MB
     each, 2.4 MB compressed). The generators, Lemon, the grammar files and the corpora stay
     in this repository. A Lean user then does not clone this repository, which is 111 MB
     without its history, because Lake clones each git dependency in full
     (`Lake/Util/Git.lean`).
   - The parser does not get a repository of its own (see "Alternatives considered").

3. **The shell variable.** Decided by the owner on 2026-11-02: `shell.nix` sets
   `BELAY_DEV_SHELL=1`, and the recipe, the test and ADR 0020, D6 use it to find the shell.
4. **The name of the `extern_lib`.** Decided by the owner on 2026-11-02: it is renamed from
   `parserShim` to a name for what it holds, in the same pull request (D2).
5. **The scope.** Decided by the owner on 2026-11-02: the files in the list of D4 are part of
   this ADR's pull request.
6. **Where the checks run.** Decided by the owner on 2026-11-02: the symbol test and the
   `ldd` or `otool -L` test of D5 run in the Nix suite that has the Lake output of the text
   package and the surface. The generation check of D3 has its own small Nix suite.

## Sources

- Lake's C compile functions: `buildO`, `buildLeanO` and `compileO` in
  [`src/lake/Lake/Build/Common.lean`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Common.lean)
  and [`src/lake/Lake/Build/Actions.lean`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Actions.lean).
- Lake's clone of a git dependency: `clone` in
  [`src/lake/Lake/Util/Git.lean`](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Util/Git.lean).
- The lakefiles of fact 10, read on 2026-10-23:
  [leanprover/leansqlite](https://github.com/leanprover/leansqlite) (lakefile and README),
  [leanprover/nauty-ffi](https://github.com/leanprover/nauty-ffi),
  [xubaiw/CMark.lean](https://github.com/xubaiw/CMark.lean),
  [acmepjz/md4lean](https://github.com/acmepjz/md4lean) (lakefile and `md4c/adhoc_include`),
  [leanprover/lean-beam](https://github.com/leanprover/lean-beam),
  [lean-dojo/LeanCopilot](https://github.com/lean-dojo/LeanCopilot) and
  [marcusrossel/lean-egg](https://github.com/marcusrossel/lean-egg).
