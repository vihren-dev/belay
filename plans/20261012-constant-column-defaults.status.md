# Constant-column-default status

Created 2026-10-12. Status: IN PROGRESS.
Task: [constant defaults](20261012-constant-column-defaults.task.md).
Source: [issue #14](https://github.com/vihren-dev/sqlite-verifier/issues/14).

## Progress

- 2026-10-12: Prepared the T14 outcome and acceptance record on accepted
  main `6441fc14`, in the reused completed `ci-split` workspace. Its previous
  checkout is retained by an archive bookmark. T18a is delivered; T07,
  T08 and T11 are preferred predecessors. Native investigation can proceed
  while T06 and PR #81 wait for owner input. No production representation
  is changed. The current and proposed resolution/default boundaries have
  been inspected before selecting native cases.

Decisions waiting for the owner:

- None for the native investigation. Final representation and codec
  changes retain the required owner review.

- 2026-10-12: Completed 260 bounded native observations across exact
  SQLite 3.51.0 and 3.46.0 pins, covering five affinities, six literal
  classes, optional NOT NULL, empty and populated tables, omitted INSERT
  values, and prohibited forms. Library hashes remain unchanged after the
  run. Raw typed cells, source identities, exact ADD commands, schema
  observations and extended error codes remain local in
  `build/20261012-column-defaults/native-defaults.json`. This is oracle
  investigation, not production-model acceptance.

  Both releases accept NOT NULL DEFAULT NULL on an empty table; a later
  omitted insert fails with the NOT NULL constraint code. They reject the
  same ADD on a populated table. CURRENT_TIMESTAMP and the probed
  expression defaults also succeed on empty tables and fail on populated
  tables. PRIMARY KEY and UNIQUE additions fail in both states. These
  findings require explicit model restrictions for unmodeled accepted
  forms, rather than invented engine errors. No production code changes.

Decisions waiting for the owner:

- None for this investigation. The existing final representation and codec
  review remains required after implementation.

- 2026-10-12: Extracted the unchanged Value declaration into a small
  core module so column metadata can use stored values without importing
  the table model. All qualified names, constructors and the declaration
  docstring retain their exact original bytes; codec source is unchanged.
  The package build list now includes the module, and its ownership test
  accounts for the additional core module. Final model-package, application
  runtime and public documentation builds pass. All 244 declarations are
  checked. Three actual isolated-package tests pass, including core/codec
  consumers and rejection of an application import. Initial missing-module
  build and wrong-runtime-root test attempts remain separate; corrected
  receipts are retained locally. No default admission or execution change
  is claimed by this foundation.

Decisions waiting for the owner:

- None for this representation-preserving extraction. T14 final default
  representation and codec changes retain their required owner review.

- 2026-10-12: Prepared constant-default metadata and codec round-trip
  cases in the model suite. The edits are uncommitted and unvalidated.
  The resource guard stops further validation at 9.95 GiB free, below the
  10 GiB requirement. A precise cleanup proposal selects only the completed
  T06 installed test's extracted Nix cache, 1,114,598,749 bytes. The
  original offline archive is retained and its checksum is verified; no
  source, installed runtime, GC root, test result or campaign record is
  selected. The enclosing directory has no open file handles. It is newer
  than the standing 24-hour allowance, so targeted approval is requested
  in `build/20261012-column-defaults/cleanup-proposal.json`. No deletion
  or validation occurs after the guard refusal.

Decisions waiting for the owner:

- Approval to delete that exact extracted cache, or hold T14 validation.

- 2026-10-12: The owner authorized the proposed cleanup. Deleted the
  completed T06 test's extracted cache after checking its identity, the
  retained archive checksum and open files. The deletion receipt records
  1,114,598,749 bytes removed. Nix garbage collection also removed 1,290
  unreachable paths and reported 851.65 MiB freed. The resource guard now
  passes with about 11.7 GiB free. Constant-default validation has resumed.
  Receipts and the garbage-collection log remain local under
  `build/20261012-column-defaults/`.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.
  The cleanup request above is resolved.

- 2026-10-12: The resumed runtime build failed before compilation because
  Nix could not connect to `/nix/var/nix/gc-socket/socket`. Its process
  exited with code 1. The initial failure is retained in
  `build/20261012-column-defaults/constant-runtime.log`. The constant-default
  edits remain unvalidated and uncommitted. Validation is held under the
  workspace rule for build-environment failures.

Decisions waiting for the owner:

- Retry the unchanged build once, or hold validation.
- Final review of the completed T14 representation and codec changes.

- 2026-10-12: The owner authorized one unchanged build retry. It passed
  and produced the complete runtime at
  `/nix/store/87dky0aaqs8xw5xw00nm5qgp27v1jzpb-sqlite-verifier-runtime-1`.
  ColumnDefault now retains a typed constant Value, and the codec derives
  scalar instances before the default instances that use them. Five scalar
  round trips and four corrupt-input refusals pass through compiled Lean
  checks. Together with the existing shared-shape checks, 15 tests pass.
  Another 15 suite-ownership and frontend-import checks pass. The checked
  public documentation covers all 245 declarations. Original and retry
  logs and test XML remain separate under the local build directory.
  This checkpoint adds representation and transport only; SQL admission,
  default execution and complete T14 acceptance remain unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.
  The build-retry request above is resolved.

- 2026-10-12: Independent review `20261012T094050Z-cc166681`
  reports the expected codec owner-review gate and one documentation
  omission. Updated the format guide with the constant payload, its
  affinity-applied meaning and an example. Final owner review is deferred
  until the complete T14 change is ready, as authorized in the task queue.
  This does not count as owner approval or completed T14 acceptance.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Review of the format correction found no must findings
  and one wording ambiguity. Clarified that each scalar default payload
  must be inside the constant wrapper; bare scalar values are not default
  encodings. Recorded the finding as fixed.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Corrected the format guide's positional reference to
  the value encodings below. The wrapper clarification review had no
  must findings and identified this reference as a should finding.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Final format-guide correction `1506856f` passes
  independent review `20261012T094328Z-1506856f` with no findings. The
  representation and transport checkpoint is committed and checked.
  Default execution, SQL admission, native conformance, preservation
  lemmas and end-to-end acceptance remain to be implemented.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Structural column extension now appends each stored
  constant default. Absent defaults still append NULL. Current-timestamp
  metadata is not evaluated; current SQL admission continues to exclude
  it and all new default syntax. Replaced the NULL-only row operation and
  projection helper with value-based operations, updating their callers
  and exact plain-words statements. Row identity, old-cell preservation,
  extension composition, table validity and old-field projection proofs
  compile. The new-column projection theorem applies to arbitrary stored
  constants and arbitrary old-field lists under width and freshness
  assumptions.

  Final runtime and documentation builds pass; all 246 declarations have
  checked documentation. Thirty-two existing codec, shape, ownership and
  frontend checks pass. The new compiled default-extension check passes
  after correcting fixture indentation, covering all five scalar storage
  classes, plain NULL extension, empty rows and both projection lemmas.
  Failed fixture attempts remain separate from corrected results. Logs and
  XML are local under `build/20261012-column-defaults/`. No native
  conformance, default SQL admission or complete T14 acceptance is claimed.

  The resource guard then failed at 9.52 GiB free. Used the owner's
  standing Nix garbage-collection authorization: removed 1,254 unreachable
  store paths and reported 1,342.64 MiB freed. The guard passes again.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Independent review `20261012T094947Z-d7006a12`
  has no must findings and requests a checked Column.extensionValue
  reference in the ADD-column theorem's plain-words statement. Prepared
  that correction. The resource guard refuses further builds at 9.74 GiB
  free. A documentation build was mistakenly launched after the refusal;
  it was stopped with SIGINT and exited with code 1. It is not acceptance.
  The correction remains unvalidated and uncommitted.

  A precise proposal selects eight superseded build symlinks, retaining
  the latest checked runtime and documentation links, all source commits,
  logs, XML and original archives. Unlinking them and then collecting
  unreachable Nix paths requires the requested targeted approval because
  T14 is still active. The proposal remains local at
  `build/20261012-column-defaults/superseded-links-cleanup-proposal.json`.

Decisions waiting for the owner:

- Approve the eight listed symlinks for cleanup, or hold validation.
- Final review of the completed T14 representation and codec changes.

- 2026-10-12: The owner approved the eight-link cleanup. Verified
  each symlink's inode and target before removing exactly the listed links.
  The current checked runtime and documentation remain retained. Nix
  garbage collection removed 50 unreachable store paths and reported
  1,446.01 MiB freed. The resource guard passes with about 11 GiB free.
  The approved cleanup receipt and garbage-collection log remain local.
  Resumed compilation of the pending checked docstring reference.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.
  The eight-link cleanup request is resolved.

- 2026-10-12: The resumed documentation build passes and checks
  all 246 public declarations. The ADD-column theorem now names
  Column.extensionValue through a checked Verso reference, resolving
  review finding `20261012T094947Z-d7006a12#1`. The interrupted pre-cleanup
  attempt remains separate from the successful approved retry log.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Docstring correction `52c3fc14` passes independent
  review `20261012T103240Z-52c3fc14` with no findings. The resource guard
  still passes. Default SQL admission and complete T14 acceptance remain
  unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Integrated main `5feb549e`, including delivered
  resolution core PR #81 and the accepted development-integrity policy.
  Retained the complete previous T14 checkout and pending review record
  under `archive/t14-before-resolution-integration-20261012`. Resolved
  the package list by retaining both resolution and the scalar Value
  module; the actual public import closure now contains 35 modules.

  Complete runtime and checked documentation builds pass. The inventory
  checks all 484 declarations. All 36 affected checks pass against the
  integrated runtime: exact constant extension, codec refusal and round
  trips, shared shape, neutral consumers, actual isolated package builds,
  forbidden application imports, suite ownership and frontend imports.
  Fresh logs and XML are in `build/20261012-t14-main-integration/`.

  The preceding untracked build directory was absent when integration
  validation began. Earlier raw T14 logs and native observations were not
  found in the workspace or local artifact directory. Source and status
  commits remain intact. Fresh checks above establish current integration
  acceptance only; the old raw native campaign must be regenerated before
  it can support final T14 acceptance. No cause for the disappearance is
  inferred. Free space is about 26 GiB and the resource guard passes.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Integration `c08ae90a` passes independent review
  `20261012T105613Z-c08ae90a` with no findings. Current main and the T14
  representation/projection changes now build together. Default SQL
  admission, the production resolution switch and full acceptance remain
  unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Added model-owned native oracle comparisons for six
  literal fixtures and five affinities on exact SQLite 3.51.0 and 3.46.0
  pins. Independently authored stored default metadata drives our Lean
  row-extension operation; native rowids and typed old/new cells supply
  the expected results. All 60 cases pass. Fifteen suite-ownership and
  frontend-import checks pass. The complete macOS model suite passes
  126 tests in its Nix sandbox, with fresh XML retained in its output and
  the local integration evidence directory. This validates structural
  extension given resolved metadata, not SQL admission or resolution.

  The owner starts ADR 0010 independently. Updated T14 acceptance to
  consume its case layout, proofs project, installed Lake packages and
  cache controls. This task does not duplicate that orchestration work.
  Model work continues; final command-line acceptance follows the relevant
  delivered interfaces. Existing source verify checks remain only while
  that deprecated command exists.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Native-comparison checkpoint `473b6d72` passes
  independent review `20261012T110554Z-473b6d72` with no findings. The
  complete 126-test macOS model suite and 60 direct native comparisons
  are acceptance for row extension given resolved defaults. SQL admission
  and the remaining end-to-end acceptance remain unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Regenerated native boundary evidence in
  `build/20261012-t14-default-phases/`. The bounded probe completes 280
  observations on pinned SQLite 3.51.0 and 3.46.0: fourteen ADD forms,
  five affinities, and empty or populated tables. The resource guard passes.
  Results retain each library path, binary hash, source identity, preparation
  code, step code, typed rows and omitted-insert result. The results file
  SHA-256 is `6b88bf5b7e1a8fbd811c59510ed6295a606d50bd4d978e83014a74f2a47dc139`.

  Both versions prepare NOT NULL DEFAULT NULL and the probed nonconstant
  defaults successfully. They accept the ADD on empty tables and fail at
  step on populated tables. PRIMARY KEY and UNIQUE additions fail during
  preparation for both table states. The ten subsequent omitted inserts
  into NOT NULL DEFAULT NULL columns fail with code 1299 as expected; these
  are recorded SQL refusals, not diagnostic failures. No diagnostic fails.

  The comparison expression DEFAULT (1=1) exposes a current resolution
  defect: constantDefault classifies it as nonconstant, and resolveAddColumn
  predicts a preparation error. Both engines prepare it successfully and
  accept it on an empty table. Admission work must correct this distinction
  while retaining supported-domain refusal for expressions the model does
  not evaluate. This evidence determines the next change; it is not an
  additional passing model test or completed T14 acceptance.

  Corrected the current task's stale statement that PR #81 awaits review.
  It is merged; the production resolution switch remains unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Corrected default preparation classification in the shared
  resolution context. Constant comparisons now pass preparation eligibility;
  identifiers nested inside signs or comparisons fail it. A bare identifier
  keeps SQLite's default-text behavior. ADD resolution still refuses these
  unmodeled defaults through its supported-domain check instead of inventing
  a preparation failure. CREATE resolution uses the same corrected predicate.

  Sixteen new model-owned regressions compare the predicate and actual ADD
  resolution with preparation on both pinned native engines. The comparison
  case fails against the retained pre-fix runtime for the intended predicate
  mismatch. All sixteen pass with the correction. The final runtime builds,
  all 485 public declarations pass checked documentation, and the complete
  macOS model suite passes 142 tests in the Nix sandbox. Eleven test-ownership
  and frontend checks also pass. Evidence is retained under
  `build/20261012-t14-default-phases/`; final runtime, documentation and model
  outputs are linked as `build/t14-resolution-final` and its numbered outputs.
  No Linux acceptance or completed default execution is claimed.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Independent review of `833da85c` found that SQLite treats
  unquoted TRUE and FALSE as constants inside default expressions. Added
  that exception with case normalization and five more syntax fixtures,
  including quoted names. Both review findings are recorded as fixed.
  The predicate and ADD resolver now pass all 26 native comparisons.

  The first expanded suite exposed a test proof that ordinary decide could
  not reduce through identifier normalization. Evaluated results matched
  SQLite. Changed the assertion to kernel reduction and reran acceptance.
  The final sandboxed macOS model suite passes all 152 tests. The runtime
  builds and checked documentation covers all 485 public declarations.
  Final outputs use `build/t14-resolution-reviewed`; logs are in
  `build/20261012-t14-default-phases/reviewed-build.log`. Earlier failed
  attempts remain in the evidence directory and are not counted as passes.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Review of `6256d886` confirms both earlier findings are
  fixed. It requests a named predicate for SQLite's boolean keyword names.
  Extracted booleanKeywordName, which normalizes the name once, and recorded
  that finding as fixed. The final runtime and documentation build; all
  486 public declarations have checked documentation. All 26 default
  resolution comparisons pass against this runtime. The preceding full
  152-test model result remains evidence for the semantic correction;
  the predicate extraction has a fresh build and focused regression run.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.

- 2026-10-12: Predicate cleanup `041748db` passes independent review
  `20261012T113727Z-041748db` with no findings. All findings from this
  default-classification correction are resolved. Constant-default SQL
  execution, the production resolution switch, and complete T14 acceptance
  remain unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: PR 115 is merged as 780fb214. The storeValue dependency is
  delivered. The task file now names the delivered Syntax.Expr default
  representation and Row.Stored requirement. The next production change
  must preserve stored form for old rows extended with a constant default.
  This workspace still contains the reviewed classification work at 4a4f3f56;
  it has not been integrated with 780fb214. The older validation records do
  not establish acceptance on current main.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Preserved the earlier T14 line at bookmark
  archive/t14-before-store-value-integration-20261014 (bad64185), then started
  the current change from merged main 780fb214. The old resolved-default
  field and conversion implementation remain historical work on that line.
  The active task uses Syntax.Expr and the delivered storeValue instead.

  Ported the reviewed preparation correction and its 26 native comparisons.
  Constant equality defaults are eligible; unknown names nested in signs or
  equality are not. Unquoted TRUE and FALSE remain constant keywords. Other
  expression forms keep main's existing permissive classification followed
  by model restriction. This change does not add default execution.

  The retained test first fails against the unchanged default classifier in
  the T08 integration runtime: SQLite prepares DEFAULT (1=1), but the model
  reports defaultNotConstant. The corrected implementation passes the full
  sandboxed macOS model suite: 133 tests in 156.54 seconds, including all 26
  comparisons. Runtime libraries and all 790 checked public declarations
  compile. Twelve suite-ownership and frontend checks pass. The protected
  verdict has unchanged agreement counts and lock, with no disagreements.

  Logs: build/t14-default-main-regression-checked-20261014.log,
  build/t14-main-classification-20261014.log,
  build/t14-main-source-20261014.log and build/t14-main-verdict-20261014.log.
  The first regression command used another workspace's runtime symlink,
  which made pytest load both conftest files. Using the immutable store path
  fixed that invocation; it is not counted as a product failure. Independent
  review of this port follows its commit. Full default execution and final
  cross-platform acceptance remain unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Commit d4aee20e passes independent review
  20261014T155709Z-d4aee20e with no required findings and two documentation
  recommendations. Fixed both: callers check quoting, and the predicates
  describe SQLite's constant-default preparation rule within their stated
  classification scope. Both findings have resolution records. Public
  documentation compiles in build/t14-main-review-docs-20261014.log.
  Implementation and test behavior are unchanged from the passing 133-test
  run. The documentation correction requires its own independent review.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Documentation correction 7044c7d6 passes review
  20261014T155857Z-7044c7d6 with no findings. The preparation correction on
  current main is tested and reviewed. The task bookmark records this
  checkpoint. Constant-default admission, execution, preservation and
  installed acceptance remain unfinished. The older implementation and
  evidence remain on the archive bookmark named above.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Added a shared literal-default evaluator in Resolution/Defaults.lean
  and moved defaultValue out of Writes.lean. It evaluates NULL, numeric, text
  and blob literals, signed numeric literals and bare identifiers, including
  the TRUE/FALSE exception. Time values and compound expressions retain model
  restrictions. No resolved-default metadata or second affinity implementation
  was added. INSERT's existing fullRow applies storeValue after this evaluator.

  Ten native-comparison tests cover 12 defaults across five affinities and
  both pinned engines: 120 comparisons of omitted INSERT values and storage
  classes. They fail against the prior runtime's unmodeledDefault refusal and
  pass against the new evaluator. All 25 focused comparisons and package,
  ownership and frontend checks pass. All 143 sandboxed macOS model tests pass.
  Runtime libraries and all 791 public declarations compile. The protected
  verdict retains its agreement counts and lock, with no disagreements.

  The first build exposed the old proof assumption that defaultValue fails
  only with model restrictions. The corrected proof also covers the numeric
  literal preparation error for an oversized hexadecimal literal. Its initial
  tactic attempt failed; the checked correction reduces the numeric conversion
  before splitting its result. A test import from the old column codec was
  corrected to conformance.case_format. These failures are not passing checks.

  Evidence: build/t14-literal-defaults-before-checked-20261014.log,
  build/t14-literal-defaults-final-20261014.log,
  build/t14-literal-defaults-focused-20261014.log,
  build/t14-literal-default-model-20261014.log and
  build/t14-literal-default-verdict-20261014.log. Independent review follows
  the commit. SQL catalog admission still refuses these literal defaults;
  ADD COLUMN execution and preservation are not changed by this unit.
  Those integrations and final cross-platform acceptance remain unfinished.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Review 20261014T161238Z-4c9108df found no required changes
  and two recommendations for the hexadecimal error path. The documentation
  now identifies this as SQLite's preparation error. Four new comparisons
  cover positive and negative oversized hexadecimal defaults on both engines.
  SQLite accepts each table definition and rejects the omitted-value INSERT
  during preparation; fullRow produces the matching preparation error and
  message. All four pass in build/t14-literal-hex-review-checked-20261014.log.
  The first test attempt imported a conformance module outside the fixture's
  library path; the corrected test imports the model's error messages directly.

  All 791 public declarations compile in
  build/t14-literal-review-docs-20261014.log. Both findings are recorded as
  fixed. Production behavior is unchanged from the passing 143-test run;
  the four added cases have fresh focused results. Independent review of
  this correction follows its commit.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Correction 80873314 passes review
  20261014T161540Z-80873314 with no findings. The shared literal-default
  evaluator, its error proof and native comparisons are tested and reviewed.
  Next acceptance remains SQL catalog admission, ADD COLUMN row extension
  with stored-form preservation, and the installed example on both platforms.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: GitHub main advanced to c10fe001, the merge of PR 116.
  Integrated it before extending catalog admission. It supplies the approved
  obligation and row-write corpora, their claims and lock, and includes both
  corpora in the frozen test inputs. These files exactly match merged main;
  this task adds no judge or claim change. The merge has no conflicts.

  The protected verdict passes, including all 24 row-write cases in corpus 11
  and the two correctly unsupported obligation cases in corpus 10. Existing
  corpus counts are unchanged. The sandboxed macOS frozen suite passes.
  Evidence is in build/t14-pr116-verdict-20261014.log and
  build/t14-pr116-frozen-20261014.log. Catalog-admission code is unchanged
  at this checkpoint; integration review follows the commit.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: Integration e30196a9 passes independent review
  20261014T162046Z-e30196a9 with no findings. The frozen suite passed all
  146 tests in 68.46 seconds. The active bookmark includes the approved
  corpus update. Catalog admission and ADD COLUMN execution remain next.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-14: The resource guard stopped new build work at 9.62 GiB free.
  Under the owner's standing cleanup approval, Nix garbage collection
  deleted 118 unreachable store paths and freed 5,386.12 MiB. Every deletion
  is recorded in build/t14-space-cleanup-20261014.log. No workspace test
  directory or retained build link was deleted. The resource guard passes
  after cleanup. Catalog-admission implementation has not started yet.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-15: Catalog admission builds, including the 791 checked public
  declarations. Its focused run fails all five affinity parameters; 15 other
  checks pass. The first NULL-default case disagrees because Native.columnMatches
  and Predict.nativeColumn still handle only CURRENT_TIMESTAMP. This is not a
  passing feature checkpoint. The admission edits remain in the working copy.

  A bounded probe with the pinned runtime confirms that X'00ff' and x'00FF'
  produce the same expression tree but different native default metadata.
  The same loss occurs for - 7 and -7. Bracketed and backtick-quoted true
  also lose their quote kind. Evidence is in
  build/t14-default-spelling-20261015.json. The next change must preserve
  source spelling through syntax, codecs and catalog before extending the
  two conformance adapters. The judge and its lock remain unchanged.
  The pending admission test now includes these spelling cases.

  Build and failure logs are build/t14-default-admission-build-20261014.log
  and build/t14-default-admission-focused-20261014.log. The initial spelling
  probe used unsupported INSERT DEFAULT VALUES; its corrected run uses
  SELECT and all ten cases reach the frontend successfully.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-15: The working copy now carries each default's source text from
  frontend syntax through the catalog to Native.columnMatches and
  Predict.nativeColumn. The judge and native recorder are unchanged.
  The runtime builds, the generated-source round trip passes, and all 795
  public declarations have checked documentation. A constructor-based Repr
  fixes invalid indentation from printing the new nested default record.

  The focused run passes 48 frontend checks. For each of five affinities,
  the first 11 admission cases agree and their generated terms pass the
  kernel. This includes the previously lost blob casing and sign spacing.
  All five parameters then fail at the bracket-quoted [true] default.
  The expression tree marks it as not double-quoted, so the literal evaluator
  still treats it as the boolean keyword. Preserve this quote distinction
  in default evaluation next. The changed transport also needs its version
  updated before acceptance. Production and test edits remain uncommitted
  because the admission suite is not yet passing.

  Evidence: build/t14-default-spelling-build-20261015.log and
  build/t14-default-spelling-focused-20261015.log (five failed, 48 passed
  in 89.03 seconds). The temporary generated-source diagnostic was removed.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-15: Written default evaluation now treats bracketed and backtick
  identifiers as text. The error-preservation proof compiles. Script records
  use version 3, and conformance cases use version 5 to identify the changed
  default syntax. Retained native records are unchanged. Their replay tests
  permit only the transport version difference; all other fields must match.

  The focused run passed all 54 tests in 137.97 seconds, including 85
  admission cases with kernel checks and a mutation that changes default
  spelling without changing blob bytes. The broader harness passed all 179
  tests in 6.21 seconds after its version assertion and restriction example
  were corrected. CURRENT_DATE now exercises the unmodeled-default restriction.

  The full model run is still active. Its retained-fixture assertions used
  the old version and failed; the assertion correction is in the working
  copy for the next run. Remaining model checks have reached the new admission
  tests. Do not treat this run as passing. Build and test evidence is in
  build/t14-quoted-defaults-build-20261015.log,
  build/t14-quoted-defaults-focused-20261015.log and
  build/t14-default-admission-acceptance-20261015.log.
  Full model revalidation, generated-input checks, protected verdict and
  independent review remain before the feature commit is accepted.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.


- 2026-10-15: Literal catalog admission is ready for independent review.
  The sandboxed macOS model suite passes all 153 tests in 343.59 seconds.
  The harness passes all 179 tests, and the 16 generated-input parity checks
  pass in 19.30 seconds. All 796 public declarations have checked documentation.
  The protected verdict passes with unchanged corpus counts. The judge, claims,
  lock and retained native records are unchanged.

  Evidence: build/t14-default-admission-final-20261015.log,
  build/t14-default-generated-inputs-final-20261015.log and
  build/t14-default-verdict-20261015.log. The first generated-input invocation
  selected the conformance runtime, which excludes examples. The passing run
  uses the complete runtime. This was a test invocation correction.

  This checkpoint admits literal defaults in catalog schemas and supplies
  omitted INSERT values. Source spelling survives syntax, codecs, catalog
  comparison and prediction. Quote delimiters distinguish literal text from
  boolean keywords. A source-spelling mutation with equal blob bytes is rejected
  by the catalog comparison and has a kernel-checked disagreement.
  ADD COLUMN row extension, preservation proofs, installed examples and final
  two-platform acceptance remain. Independent review follows this commit.

Decisions waiting for the owner:

- Final review of the completed T14 representation and codec changes.
