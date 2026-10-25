# S7: SQL files, named statements and build freshness

Created 2026-10-24. Status: OPEN. Implementation follows task review.
Status: [progress](20261024-surface-s7-files.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), D1/S7 and D6;
[ADR 0016](../docs/adr-0016-model-and-surface.md), surface/tool boundaries.
The target guide's SQL-file behavior is restated here. Proof-cost reporting
and checked doc blocks have separate tasks; this task alone does not finish S7.

## Purpose and accepted decision

Users can elaborate inline SQL, but cannot use their existing SQL files or
detect a compiled declaration that still contains an older file. S7 supplies
these guide requirements through the existing translator, Script and resolver.
The owner's ADR17 completion request includes the guide's separate SQL and
application libraries, with Belay as a dependency. The library selector serves
that current multi-library example. Dependency and relocated-copy fixtures
verify the promised package-relative paths when the same package is consumed
elsewhere; a compiler-working-directory path would break that public contract.

On 2026-10-24 the owner accepted exact SQLite metadata and native Lake tracking.
Expression spelling can be a result-column name; whitespace and comments can
therefore change semantics. Neither this task nor the guide may promise that
such edits never rebuild importers. Source positions stay outside Script;
semantically significant text stays inside it. No semantic cache is required.

On 2026-10-25 the owner accepted an explicit package-root override alongside
automatic discovery. Pinned Lake's module setup identifies the package but
does not disambiguate two valid nested projects with the same package name.
Keep these layouts supported through the explicit root; do not guess between
roots or impose a restriction on nested projects.

## Required outcomes

- **Files give ordinary scripts.** `sql_file "sql/schema.sql"` gives the same
  Script as the equivalent inline text. The path is relative to the package
  that owns the Lean source, including a dependency package loaded by a consumer.
  A nested source file or different process working directory does not change
  that root. Missing/unreadable files produce actionable errors at the form.
  Parsing and file I/O happen at elaboration, outside kernel reduction.
- **Ambiguous ownership has an explicit path.** The option
  `belay.sql.packageRoot : String` defaults to the empty string, which keeps
  automatic discovery. A nonempty value is a relative path anchored to the
  directory of the Lean source identified by `getFileName`, not the compiler's
  working directory. Invalid or unreadable roots give actionable errors;
  ambiguous automatic discovery points to the override. Expose
  `readSqlFileSourceAtRoot (root : FilePath) (package : PkgId) (path : FilePath)`
  as the explicit-root primitive beneath the convenient source loader. A root
  controls current file access, not the compiled package identity. Persist only
  package identity, package-relative SQL path/hash and module/declaration
  associations. The checker resolves that identity through the current Lake
  package mapping; an override does not bypass freshness checks or serialize
  a machine-specific root.
- **File parameters are explicit.** Every parameter, including `$name`, becomes
  a Value argument in first-appearance order. A same-named Lean local is never
  captured. Reuse the current parameter plan, number identity, sparse NULL slots,
  repeated-name behavior and collision errors; do not rewrite parameter signs.
  The existing `Script.withValues` primitive remains available for scripts
  whose parameter identities cannot use convenience argument names.
- **Named statements give named definitions.**
  `sql_module Queries from "sql/queries.sql"` defines `Queries.findByEmail`
  for a statement preceded by `-- name: findByEmail`. Immediately following
  ordinary comment lines become its docstring. One optional sqlc suffix, such
  as `:one` or `:exec`, is accepted and ignored; it does not change semantics.
  The name must be one Lean identifier; invalid, duplicate or already-declared
  names are errors. Each marker owns exactly one parsed SQL statement.
  SQL without a name, empty named entries and multiple statements under one
  name are errors. A trigger with inner semicolons remains one statement.
  Comments/empty files without named statements do not invent declarations.
- **Markers are lexical.** Strings, quoted names, block comments and trigger
  bodies containing marker-like text do not create names or section boundaries.
  Use the existing parser's statement ranges and lexical information. Preserve
  SQL text and parameter offsets when selecting a named statement or section.
- **Migration directions cannot run together by accident.** `sql_file` accepts
  `(section := "up")` and `"down"` for standalone goose `-- +goose Up`/`Down`
  or dbmate `-- migrate:up`/`down` markers. Each direction occurs at most once;
  mixed conventions, duplicate directions and missing requested directions are
  errors. A file with direction markers requires `section`; `section` on a
  file without them is an error. Text before the first direction may contain
  comments/whitespace only. A named module rejects direction markers and points
  to `sql_file` with `section`. Unknown section values are header errors.
- **Checking does not change the script.** Both forms accept `(against := db)`
  for a closed evaluable database, using the same resolution checks as `sql!`.
  Checked and unchecked forms give definitionally equal scripts/functions.
  Statements of one script see earlier schema changes; independently named
  application statements each start from the supplied database. Parameterized
  scripts retain the existing preparation contract. A broken database
  definition does not cause duplicate cascading diagnostics.
- **Errors identify the external source.** Parser, translation, parameter and
  resolution errors appear at the Lean form and identify the SQL path, original
  line/column and named statement when present. Selection never renumbers the
  file. Unicode and CRLF positions are correct. Recognized sqlite3 dot commands
  and tool syntax such as `sqlc.arg(id)` or `:v*:ids` explain that conversion is
  required; ordinary quoted/comment text containing them remains legal SQL.
- **Generated declarations are useful in the editor.** Hover includes the
  statement's documentation and SQL source location. Reuse the editor task's
  shared metadata boundary when available. Document that an external SQL edit
  requires restarting the Lean file; this task adds no external-file watcher.
- **Compiled source records survive imports.** Persist package identity,
  package-relative source path and normalized-text hash with the compiled
  module and generated declaration where there is one. Several declarations
  using a file retain their association but do not inflate source totals.
  Relocating a package does not leave the checker using an old absolute path.
  Hash normalization matches pinned Lake's `text = true` line-ending rules.
- **The checker inspects the existing build.** `lake exe belay-sql-check`
  compares recorded sources in the current package's compiled libraries with
  current files, including records reached through imported dependencies.
  It reports source totals by library, and exits zero only when every inspected
  record is fresh. A changed or missing source identifies its package/path and
  affected library with a rebuild command. Missing compiled modules/records
  that cannot be loaded are explicit errors, not evidence of zero sources.
  A library with valid compiled modules and no SQL records reports zero.
  A library selector permits checking one library in a multi-library package.
  Inspecting a stale library must not rebuild it first. Building the checker
  itself must not depend on the application's library being inspected.
- **Native Lake inputs work end to end.** The documented input_dir extension
  filter, `text = true` and library `needs` make SQL edits/additions rebuild
  the consuming library. input_file works for a single file. Unrelated file
  extensions do not change that dependency. EOL-only changes agree with Lake's
  normalization and do not produce false stale reports. Importer rebuilds follow
  native Lake artifact dependencies; no stronger guarantee is made.
- **The installed boundary contains the usable tool.** The executable and its
  required native dependencies work in the installed surface derivation and
  a consumer package. The conformance runtime remains free of the surface and
  checker. Only the separate checker tool may import Lake; `import Belay` and
  ordinary elaborator modules retain ADR16's library dependency boundary.

## Tests and acceptance

Compiler fixtures exercise both forms through `import Belay`, a schema/seed
script, independently named parameterized queries, both migration conventions,
checked/unchecked definitional equality, and the diagnostic cases above.
Include repeated and sparse parameters, `$x` beside a same-named Lean local,
sign/name collisions, comments/strings/trigger bodies containing markers,
invalid names, documentation retention, Unicode, non-BMP characters and CRLF.
An ordinary file script with no parameters must reduce to its inline Script.

A real small consumer Lake package verifies the package-root rule, including
a dependency package and relocated copies. Build it once without needs, change
SQL without touching Lean, invoke the installed checker, and establish a stale
nonzero result before any rebuild of the inspected library. Explicit rebuild
restores success. Test missing sources, missing compiled modules, several
libraries, shared source references and the library selector. With native needs,
verify changed output after an SQL edit, added `.sql` discovery, unchanged
non-SQL input and EOL normalization. Comparing TOML strings is insufficient.
Include two valid nested projects with the same package name that can compile
the same Lean file. Automatic discovery must report the ambiguity; explicit
source-relative roots must select the requested SQL file from both compiler
working directories and after relocation. Exercise the explicit-root primitive,
invalid override paths and unchanged inline behavior. Imported records and
freshness checks must still use the current package mapping and detect edits;
the root override must not produce an unconditional fresh result.

Tests use finite subprocess timeouts and the Nix surface harness. No network
fetch is needed in the consumer fixture. Each coherent commit gets focused
checks, dev-build after package changes and independent review. Two acceptance
parts are file elaboration/named statements, then installed freshness/Lake
integration. Each ends with post-review `just test-full` and `just verdict`.
Task end also runs `just test-nix` and `just test-scheduled-checks`. Only Nix
results are acceptance evidence. Frozen predictions and judge lock stay fixed.
Extend the existing layer test to reject ordinary Belay imports of Lake or the
checker, and any surface/checker dependency in the conformance runtime; allow
Lake only in the separate tool root. Check its installed executable as above.

## Existing interfaces and ownership

Reuse SqlTerm's translateText/scriptExpr, SqlParameters, Script.withValues,
EvalDatabase, SqlDiagnostics and located translator statement ranges. The inline
literal source mapper and `$` capture policy need separation from shared term
construction; file-specific forks of numbering or name resolution are excluded.

The pinned Lake provides input_file/input_dir, text normalization and lean_lib
needs. Its module setup gives package identity, not a package-root path. The
same-name ambiguity is reproduced in the S7 workspace's
`build/agent-logs/package-root-probe/same-name-ambiguity.log`; the accepted
override resolves that gap. Verify automatic and explicit roots in the actual
consumer fixture. The surface lakefile explicitly
lists modules. The Nix surface source filter currently selects Lean/manifest
files; any shipped SQL fixture must be deliberately included in its proper input.

Own new file-source/marker/registry/checker modules and tests. Reserve changes to
SqlTerm, SqlParameters, EvalDatabase, diagnostics, surface barrel/lakefile and
test manifests with editor/doc-block/proof-cost owners. Keep lexical/source
handling, semantic term construction and filesystem checking separate where
their contracts differ. Files remain below 200 lines with checked public docs.
The private guide correction is a separate coordinated change. Report a proven
specification contradiction before changing the promised behavior.
