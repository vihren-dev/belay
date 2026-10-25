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
