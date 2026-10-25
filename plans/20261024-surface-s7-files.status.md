# Status: S7 SQL files and build freshness

Created 2026-10-24. Status: OPEN. Assigned for implementation.
Task: [task file](20261024-surface-s7-files.task.md).
Specs: ADR17 S7/D6; ADR16 surface/tool boundary.

## Decisions and evidence

On 2026-10-25 the owner accepted the explicit package-root override. The task
and ADR17 now retain automatic discovery with source-relative
`belay.sql.packageRoot`, plus the explicit-root reader. Current file access
does not change persistent package/path identity or bypass the freshness
checker. The existing same-name nested-package probe supplies the observed
ambiguity; the amendment adds end-to-end override and relocation acceptance.
The first source unit below implements the override.

The 2026-10-24 owner decision keeps exact SQLite result-column metadata and
native Lake tracking, and corrects the guide's blanket importer-rebuild claim.
The source audit establishes available native Lake input and needs APIs.
Package-root discovery and stale-build inspection still need real fixtures.
No production file elaborator, registry or checker exists at the inspected base.

Proof-cost reporting is required S7 scope and will have a bounded collector
prototype followed by its implementation contract. Checked SQL doc blocks have
their own reviewed task. Neither is silently excluded by this task boundary.

## Progress

- 2026-10-24: specified file semantics, lexical marker behavior, source records,
  installed checker and incremental consumer acceptance. Review
  `20261024T140732Z-6d8ca3d2` had no musts and two shoulds. Added the explicit
  layer check and named the current multi-library and package-path requirements
  behind selection/relocation tests. Await follow-up review and an agent slot.
  Reserve shared helpers with editor/doc-block tasks before concurrent work.
- 2026-10-24: follow-up review `20261024T140930Z-09c30b41` is clean.
  Assigned to `text_build_boundaries` in `sqlite-verifier-s7-files`, based on
  complete execution integration `5bc323f0`. Readiness audit found no new
  specification conflict. The first unit covers shared parameter construction,
  external-source diagnostics and package-root loading. Reserve SqlTerm,
  SqlParameters, SqlSource, EvalDatabase and SqlDiagnostics for this work;
  preserve current inline behavior and S5 metadata. S5 owns Check*, Sampling*
  and ReplayScript. Editor and doc-block work remain unassigned. Source review
  at the first checked commit waits for the owner's reviewer login refresh.
- 2026-10-24: first-unit source is at rest after shared inline/file parameter
  planning, one script constructor, external UTF-8/CRLF diagnostics and
  manifest-based package discovery. No public file syntax is exposed before
  migration-section safety is implemented. The package ID comes from Lean's
  setup; manifest dependency paths also support renamed dependencies. The
  ordinary consumer fixture uses real package directories with linked installed
  entries and the producer's pinned parser-library environment.
  Focused Nix run 1 passed 20 parameter, replay, diagnostic and layer cases;
  its consumer case failed before elaboration because of the fixture's package
  symlink layout. Retry 2 exposed the fixture's omitted parser-library variable;
  retry 3 corrected an environment-expression type error before building.
  Retry 4 passed the owning-package case (1 passed, 93 deselected) at
  `/nix/store/hs6b8p1fzvl2cm9hm758f16qrbc7pygk-sqlite-verifier-test-surface-1`.
  It covers an aliased dependency without its own manifest, a nested unrelated
  lakefile/manifest, Lake's actual setup from another compiler working directory,
  and a relocated copy. Logs are `build/agent-logs/s7-files-nix-surface-{1,2,3,4}.log`.
  The two required local development builds passed; they are diagnostics, not
  acceptance evidence. Full/verdict and task-end gates have not run.
- 2026-10-24: a local source probe found an ownership ambiguity that current
  metadata cannot resolve: two consistent nested Lake packages with the same
  original name can compile the same Lean source. The nested build passes;
  the outer consumer's actual build then finds two roots. The Lake-generated
  manifest and both command results are retained in
  `build/agent-logs/package-root-probe/same-name-ambiguity.log` as diagnostic
  evidence. The owner accepted the proposed source-relative root option and
  explicit-root reader on 2026-10-25 (decision above). First-unit source
  commit/review was pending that decision and the reviewer OAuth login failure.
- 2026-10-25: first source unit (reader, external-source diagnostics, file parameter
  mode, package-root override) merged the accepted decision `320ae77f` into this line
  by a new merge commit. Planning-line text won where the task/ADR was newer there;
  this line's text won where its recorded progress was newer (add/add status files).
  `SqlFileSource` now has `readSqlFileSourceAtRoot` (explicit root; rejects absolute
  and `..` paths and non-directory roots) beneath `readSqlFileSource`. The new
  `SqlFileLoad` registers `belay.sql.packageRoot` (empty = discovery; relative root is
  anchored at the Lean source's directory; absolute, missing and non-directory roots are
  errors naming the option) and `loadSqlFileSource`. Ambiguous or missing discovery now
  names the option. Records keep only package and relative path. Shared fixture helpers
  moved to `tests/sql_file_support.py`.
  Focused Nix surface run 3 (28 passed, 72 deselected, 32.18 seconds) at
  `/nix/store/cqjd5fgjf5njplqnvmalndv962q5zkf1-sqlite-verifier-test-surface-1`
  covers the 20 earlier parameter, replay, diagnostic and layer cases, the owning-package
  consumer, the explicit-root primitive, option anchoring from another working
  directory, three invalid roots, and two valid nested projects of one package name:
  discovery reports the ambiguity, `..` and `.` select either SQL file, an editor-style
  compile from another directory works, and a relocated copy builds. Earlier runs failed
  only on a fixture import (`build/agent-logs/s7-unit1-nix-surface-1.log`). The local
  dev-build passed (diagnostic). Public syntax, sections, registry and checker, and the
  full/verdict gates, have not run.
- 2026-10-25: review `20261025T052312Z-2e0045b5` of the first unit had two musts
  (root and unreadable-file messages lacked a corrective action) and two shoulds
  (a missing return annotation; a stale status entry). All four are fixed. The repeated
  focused Nix surface run passed 28 tests (72 deselected, 33.48 seconds) at
  `/nix/store/yl9vrf7m795jx6g517z61nk113zz1f8y-sqlite-verifier-test-surface-1`.
- 2026-10-25: review `20261025T052543Z-3ec66599` of the refactor had no musts and one
  should (R11: no assertion for the guidance text); the root and file tests now require
  the full guidance, and a focused Nix run passed 28 tests (72 deselected, 32.31 seconds)
  at `/nix/store/avm4lbjribzp4gj7srk47lfmylgix36d-sqlite-verifier-test-surface-1`.
- 2026-10-25: part 1 source (file elaboration and named statements). `sql_file "path"`
  gives the script that `sql` gives for the same text (`$name` is an argument in a file,
  and a Lean variable only inline), with `(section := "up"|"down")` for goose and dbmate
  files and `(against := db)` for the resolution errors of `sql!`. `sql_module Name from
  "path"` defines one declaration per `-- name: ident` marker, documented with the marker
  comment lines and `SQL source: path:line:col`. Comments and quoted text are found with a
  byte lexer that follows SQLite's tokenizer, so a marker inside a string, a block comment,
  a trigger body or a statement's own trailing comment names nothing. Refusals give one
  error at the form with the SQL position: direction markers without a section, a section
  without markers, unknown section, mixed conventions, a repeated or missing direction,
  SQL before the first marker, unnamed SQL, empty or multi-statement entries, malformed,
  dotted and duplicate names, already declared names, and a parse failure. The parse
  failure explains sqlite3 dot commands and sqlc macros at the refused offset; `:v*:ids`
  parses as multiplication and cannot be recognized. A file with only comments declares
  nothing. Fixtures: `tests/surface/SqlFileForms.lean`, `SqlFileErrors.lean` (checked
  with `#guard_msgs`, which also rejects extra messages, such as a cascade from a broken
  database), `SqlFileLayoutChecks.lean`, over `tests/surface/sql_files/`; CRLF, non-BMP
  and Unicode positions in `tests/surface_sql_file_forms_test.py`. The layer test now
  rejects Lake and checker imports from ordinary modules. Focused Nix surface run (36 passed,
  72 deselected, 44.51 seconds) at
  `/nix/store/xvq8rwx1vp16a7g19v04wc2gqgw5n985-sqlite-verifier-test-surface-1`; the local
  dev-build passed (diagnostic). `just test-full` and `just verdict` have not run. The
  registry and checker (part 2) have not started.
- 2026-10-25: review `20261025T054227Z-4381e26f` of the part 1 source had five musts
  (two catch-all cases over marker kinds; repeated-direction, missing-direction,
  name, empty-entry, duplicate-option and already-declared errors lacked a corrective
  action) and one should (fixture declarations without docstrings). All are fixed:
  every constructor is matched, each message names what to change, and the fixture
  expects the new text. Focused Nix surface run (18 passed, 90 deselected, 6.43 seconds)
  at `/nix/store/wbzz07xysl7gxm6bc8nkd2fjj6bi6q5m-sqlite-verifier-test-surface-1`.
- 2026-10-25: review `20261025T054500Z-f420fa5b` of the corrective-action refactor had
  no musts and one should (no test for the duplicate-section message); the errors fixture
  now checks it with `#guard_msgs`; the part 1 acceptance entry below records the gates.
- 2026-10-25: part 1 acceptance (file elaboration and named statements) after the
  reviews above: `just test-full` passed (472 passed, 71 deselected, 49 subtests in
  165.41 seconds for the main suite; 108 passed in 327.35 seconds for the surface suite;
  reports at `/nix/store/pll1s1p34sxqzp78gav75rzn19f49bii-sqlite-verifier-test-reports`)
  and `just verdict` passed at
  `/nix/store/fdyxvw89hvk8i7sa232c6is81sczb24d-sqlite-verifier-verdict`. Logs are
  `build/agent-logs/s7-part1-test-full.log` and `s7-part1-verdict.log`. Part 2 (record
  registry, checker, native Lake integration) starts next.
- 2026-10-25: decision (coordinator, owner's rule that native SQLite is the authority):
  tool syntax that SQLite parses as valid SQL gets no hint. The task text no longer
  lists `:v*:ids`, and records the pinned sqlite3 3.51.0 probe. Open integration point:
  S5 will change `SqlTerm.variableValue` to original/coerced pairs; `scriptTermFromPlan`
  here takes `variables : List (ParameterSource × Expr)` and `fileScriptTerm` needs
  a one-line adaptation when S5 and S7 are integrated (the coordinator handles it).
- 2026-10-25: part 2 starts. `Belay/Sqlite/SqlSourceRecord.lean` (no Lake import) defines
  `SqlSourceUse` (package, package-relative path, hash, optional declaration),
  `sqlTextHash` (`String.hash` of the CRLF-to-LF text, the rule of Lake's `text = true`
  inputs), source identity ignoring the declaration, and a persistent extension that
  accepts additions from any elaboration branch (`asyncMode := .sync`; it is never read
  during elaboration). `loadSqlFileSource` adds a record with the declaration being
  elaborated, and `sql_module` adds one per generated definition. Fixtures now check
  that `(against := db)` leaves a file and the module definitions `findByEmail`, `insertUser`,
  `trig` and `last` definitionally equal
  to the unchecked form. Focused Nix surface run (35 passed, 75 deselected, 54.01 s) at
  `/nix/store/v2ihkpky37iwvld5f6xji2m6p4izwc33-sqlite-verifier-test-surface-1` covers
  the pure checks and a real Lake build where an importing module reads the records of
  `Queries` (package, relative path, normalized hash, two declarations of one file, one
  declaration per module entry, distinct sources counted once). The checker, its report
  and the Lake input fixtures are next. Review of the planning amendment `a613a42e` and
  of `561834a0` found no musts (one should about a stale status phrase, fixed).
- 2026-10-25: the checker. `lake exe belay-sql-check [--library NAME]` (`BelaySqlCheck.lean`,
  the only module that imports Lake; `lean_exe` with `supportInterpreter` because loading a
  lakefile runs the interpreter) loads the workspace from the existing manifest (a missing
  manifest is an error, so it never writes one), walks the compiled modules of each library
  of the root package and every module they import (the workspace decides the olean file,
  because the model, text and surface packages share the root `Belay`), decodes the stored
  `SqlSourceUse` records, compares each distinct source with the file in its owning package
  (`pkg.dir / path`, found by the package's original name), and prints
  `library L: N modules, M SQL sources, K stale`, one line for each stale source with its
  package, path, declarations and `lake build L`, and a note that `lake build` rebuilds after
  an SQL edit only if the library lists the SQL files as `needs`. Exit 0 is all fresh; 1 a
  changed or missing source; 2 a library that could not be read (missing compiled module,
  unknown library, unknown package, no manifest). The pure report is
  `Belay/Sqlite/SqlCheckReport.lean`. The surface derivation now builds and installs the
  executable. The layer test allows Lake only in `BelaySqlCheck`. Focused Nix surface run
  (17 passed, 97 deselected, 41.29 s) at
  `/nix/store/bywr7f1nfj8p7zvdgzxg5c9l6w5k6nm7-sqlite-verifier-test-surface-1`: totals by
  library with a shared source counted once and a library without SQL at zero, the library
  selector and an unknown library, a stale source reported with no artifact touched and
  before any rebuild, a line-ending-only edit staying fresh, rebuild restoring success,
  a deleted file, a deleted compiled module as an error, records reached through a
  dependency import, and a relocated tree that checks its own dependency file. The native
  `input_dir`/`needs` fixtures are next.
- 2026-10-25: review `20261025T064316Z-54721ff5` of the checker found one must (a missing or
  unreadable compiled module gave no corrective action) and one should (test docstrings did
  not name the checked definitions); both fixed. These errors now name the library and the
  command: `lake build L` for a missing module, and deleting the damaged build files and
  `lake build L` for an unreadable one. Unknown package records also say what to change.
  `just dev-build` does not build the `belay-sql-check` executable, so the Nix surface
  derivation found a parse error that dev-build did not; run `lake build belay-sql-check`
  after edits of `BelaySqlCheck.lean`. Focused Nix surface run (16 passed, 98 deselected,
  38.29 s) at `/nix/store/0r8zvgcv5mfh5q3y1dy893xh04cy4m8m-sqlite-verifier-test-surface-1`.
- 2026-10-25: review `20261025T065939Z-426fecad` (should, R11): added the unreadable
  compiled-module case to `test_missing_files_and_missing_compiled_modules`; Nix surface run
  (1 passed, 113 deselected, 9.10 s) at
  `/nix/store/nzqzyma78kp58bf5nhgn4ayc5znffy72-sqlite-verifier-test-surface-1`. The unknown
  and ambiguous package branches stay untested (deferred): no real build reaches them
  before the module walk fails.
- 2026-10-25: native Lake input fixtures (`tests/surface_sql_lake_inputs_test.py`, in the
  `surface` suite). With `input_dir sqlFiles` (`text := true`, `.extension "sql"`) and
  `needs := #[sqlFiles]`, a library does not rebuild for an unchanged tree, an added
  non-SQL file or a line-ending-only edit (the checker stays fresh); it does rebuild for an
  SQL text edit (the checker reports it stale first, fresh after the rebuild) and for an
  added `.sql` file. With `input_file oneFile` the same holds for one file, and the library
  that does not list it does not rebuild. `CoeOut` to a build key accepts the input
  declarations in `needs`. Nix surface run (2 passed, 114 deselected, 25.08 s) at
  `/nix/store/5ppdhz8p4wbf6zdbyxb9dnh7fwcwss7r-sqlite-verifier-test-surface-1`. Layer rule 4
  already shows that the conformance runtime holds neither the surface nor the checker.
- 2026-10-25: the checker and the package-root override. Review `20261025T071945Z-0ac03732`
  (must, R19) said that the status claimed same-name project coverage that did not exist.
  The new fixture (`tests/surface_sql_check_roots_test.py`) showed a real defect: two
  nested projects of one package name, each with its own `sql/query.sql`, gave a false stale
  report, because the checker looked for every record below the package directory. A record
  now also keeps the option value and the module that set it (`SqlRootOverride`, only when the
  option is set), and the checker finds the file below the Lean file of that module. It shows
  the path relative to the package (`lean/sql/query.sql` for the nested project). Records
  without the option are unchanged. This adds data to the record that the package-root
  contract did not list (it still holds no absolute path and survives relocation); it is
  open for the coordinator to confirm. The same-name fixture is fresh after a build and
  each of the two files is stale after an edit with no rebuild. The same-name fixtures
  moved to `tests/sql_file_support.py`. Nix surface run (26 passed, 91 deselected, 69.88 s) at
  `/nix/store/47g2zk4b2fv7dy6ircmhzcnja74zgilw-sqlite-verifier-test-surface-1`.
- 2026-10-25: review `20261025T074257Z-242ef6ab` found two musts (R13). The task text now
  lists the option value and its module among the persisted data. The checker now resolves
  each record to its file and groups the records by resolved file and text hash
  (`groupSources`), so two modules that reach one file by different option values count
  one source and one stale report names both declarations (new fixture in
  `tests/surface_sql_check_roots_test.py`). Nix surface run (11 passed, 107 deselected,
  72.50 s) at `/nix/store/8klpbwk58bwck39c859rr39y6gp0a6aj-sqlite-verifier-test-surface-1`.
- 2026-10-25: review `20261025T075410Z-d34b1e68` found two musts. The persistence sentence in
  the task text now lists the option value and its module. `SqlSourceUse.sameSource` is
  deleted; `groupSources` moved into the pure `SqlCheckReport.lean` and is the one rule for
  source identity (resolved file plus text hash), tested by `#guard`s and by the records
  test. Nix surface run (22 passed, 96 deselected, 71.59 s) at
  `/nix/store/pvsk1q34r0npmprd11nrxr532fzzimgm-sqlite-verifier-test-surface-1`.
