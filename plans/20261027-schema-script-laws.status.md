# Status: schema-script laws

Created 2026-10-27. Status: OPEN.
Task: [task file](20261027-schema-script-laws.task.md).
Specs: ADR 0017 S6; the S6 automation task, part 3 outcome "the rebuild
example", and its status section "Part 3 outcome (a), the rebuild example:
stopped at a gap (2026-10-27)".

## Decisions

- 2026-10-27 (owner): option A of the S6 part 3 gap. A separate task adds the
  general step, frame, translation and success laws, then the rebuild fixture
  proves the three guide claims.

## Progress

- 2026-10-27: task specified on top of S6 automation part 3a (PR #283). The
  implementation starts on a base that contains the derived-column task.
- 2026-10-27: spec review `20261027T130038Z-837cf158` (2 musts: the frame law must exclude a
  cascade of DROP TABLE; the INSERT SELECT success law must require fitting column types). Coordinator
  error: commit d37be705, described as the fix, holds only that review record, because the edit script
  failed before it wrote the file; its review `20261027T130113Z-d37be705` has no findings, and the two
  resolutions were recorded as fixed before the fix existed. The fix is the next commit.
- 2026-10-27: review `20261027T130242Z-a51577be` (1 must: a premise on direct foreign keys does not
  exclude a cascade through other tables; fixed in the next commit).
- 2026-10-27: review `20261027T130345Z-06c93a5f` (no findings).
- 2026-10-27: slice 1 committed: the step, frame and failure laws of CREATE TABLE, DROP TABLE, BEGIN, COMMIT, the pragmas `foreign_keys` and `foreign_key_check`, and rename, with the table found by name (`TableByName`). Review `20261027T142434Z-f0c30a5b`: 3 musts (restatements of three drop and failure laws), fixed in the refactor commit after it. Part 1 is checked by `just dev-build` on the full tree; the Nix gates run at the end of Part 1.
- 2026-10-27: slice 2 committed: read certificates and frames by table name (the single-position form is replaced and all callers moved), and translation over several end states (`Migration.translatesAt_of_observations`).
- 2026-10-27: slice 3 committed: the success law of INSERT from a query without rules (`runScriptStep_insertSelect_success`), the productions of a plain scan, and the upsert of appended rows. The case with rules (foreign keys on, or triggers) is an open point.
- 2026-10-27: slice 4 committed: the fixtures `SchemaStepLaws`, `ControlStepExamples`, `CertificateAfterDrop`, `InsertSelectExamples` and `SchemaScriptReplays` with `tests/surface_schema_script_test.py` (in the suite `surfaceS6`, 611 s of 1200 s in the last full run of the split). The suite split (`tasks/surface-suite-split-3`) is merged below this commit.
- 2026-10-27: reviews of slices 1-4: `20261027T142434Z-f0c30a5b` (3 musts, fixed in `92d99c24`), `20261027T142801Z-92d99c24` (no findings), `20261027T142940Z-ffa67eb9` (1 should: no example of moved positions or several end states; the moved position is in `CertificateAfterDrop`, the several-end-states example comes with the rebuild fixture of part 2), `20261027T143133Z-96cffcde` (3 musts: the `InsertFits` and success-law docstrings and the coverage of `productions_scan` in this file), `20261027T143302Z-52921cdb` (4 shoulds: two fixture files over 200 lines, catch-all matches, a local result in this file). The next `refactor:` commit fixes them: the fixture is split in `SchemaStepLaws`, `SchemaDropExamples` and `SchemaCreateExamples`, and a classifier of the resolved statement replaces the catch-all matches.
- 2026-10-27: part 1 done (the general laws), bookmark `tasks/schema-script-laws-part1`, on a tree that contains the judge branch `tasks/table-rebuild-judge` (5a0aa7c3). Nix results after `just dev-build`: `just test-full` exit 0, `/nix/store/420apaq9icrvvrqkqh8f4c2hyhvh63ia-sqlite-verifier-test-reports` (suite `surface` 377 tests, 735 s; `surfaceChecks` 15 tests, 352 s; `surfaceS6` 60 tests, 606 s; no failures); `just verdict` exit 0, `/nix/store/ybwxm2l5xcq2986a43h5m106c37zjpsy-sqlite-verifier-verdict`; predictions `/nix/store/i3mh3pvjl636aym1s4231s2kcy1lizvf-sqlite-verifier-predictions`: the 55 files of the earlier base are byte-identical, and `corpus-v55.jsonl` comes from the judge branch. Review `20261027T144034Z-ece07f5d` of the refactor commit has no findings.

## Part 2: tactic rules and the rebuild fixture

Decision (coordinator, 2026-10-27): option A, all three guide claims, in the order tactic rules and claim 3,
claim 1, claim 2. The gates run once, at the end of Part 2, on a tree that contains `tasks/surface-editor-part3`.

Size (2026-10-27): the task file planned about 100 lines for the tactic rules of Part 2. The estimate for all of Part 2 is now 1100 to 1300 lines. The
reasons: (1) a proof over an abstract database needs the general "step continues" laws, because a rule needs the
step to continue (`modeled`) and nothing else gives it for CREATE TABLE, DROP TABLE, rename, BEGIN, COMMIT and the
pragmas (about 300 lines with the pragma `foreign_key_check`); (2) each new statement needs a rule for `sql_run`
and the tactic needs its premise names and roles (about 250 lines); (3) INSERT FROM a query has several executions,
so claim 1 needs a chain lemma over the branches of a send of statements (about 100 lines) and claim 2 needs a
law that a valid database fits the INSERT (about 150 lines); (4) the fixtures with the schema, the hints and the
native check (about 400 lines). Part 1 also exceeded its estimate (1900 lines against 700) for the same kind of
reason: the model has no earlier law for the statements.

- 2026-10-27: Part 2 slice 1 committed: `StepContinues` (the laws that the step of CREATE TABLE, DROP TABLE without
  rules, rename, a setting, BEGIN and COMMIT continues). The law for `PRAGMA foreign_key_check` comes with claim 2.
- 2026-10-27: review `20261027T160128Z-e44aecc8` of slice 1 (1 must: a catch-all case split in `Output.ofStep_ne_unmodeled`; 1 should: the wording of the size note), both fixed in `330639d6`.
- 2026-10-27: `tasks/surface-editor-part3` is merged into the branch (change `qsttolov`, no conflicts).
- 2026-10-27: Part 2 slice 2 committed: the rules of `sql_run` for CREATE TABLE, DROP TABLE without rules, a rename, a pragma setting, BEGIN and COMMIT (`SchemaStepRules`, `ControlStepRules`, premise names `atEnd` and `outline`, `statementKind?` reads the constructor of a pragma). The tactic closes the resolution of CREATE TABLE only with all definitions unfolded, so `closeSide` tries each hint also under `with_unfolding_all`; a variable of a rule that takes the tag of a premise name (`after`) is no premise any more. The fixtures `RebuildGuide` (schema, the rebuilds and the read of the guide) and `SchemaRuleExamples` (one program with all six kinds) are checked by `tests/surface_rebuild_test.py`, in the suite `surfaceS6`.
- 2026-10-27: Part 2 slice 3 committed: claim 3. `sql_refute` refutes `requireNameWrongEnforced preserves allSessions` (`RebuildRefutation`), and the fixture `RebuildReplays` runs the right rebuild on three databases and the wrong one on a connection with foreign keys on, for a check against pinned SQLite 3.51.0 (`tests/surface_rebuild_test.py`).

## Changes that the guide needs

The private guide (`model-user-guide.md`, the table rebuild section) is not edited here. These are the changes that the
fixtures show.

- (a) The guide says that the pinned profile enforces foreign keys, and gives a counterexample for the wrong rebuild
  on a fresh connection. A fresh connection has foreign keys off, in the model and in pinned SQLite, so the wrong
  rebuild keeps the sessions there. The counterexample needs `PRAGMA foreign_keys = ON` before the rebuild, as an
  application that uses foreign keys has it: `requireNameWrongEnforced` in `tests/surface/RebuildGuide.lean`, refuted
  by `sql_refute` in `RebuildRefutation.lean`, and replayed on pinned SQLite in `RebuildReplays.lean` (`wrong-enforced`).
- (b) The claims "preserves" and "succeeds" about the right rebuild hold for the databases that have the tables of
  the guide's schema, not for every database. A database without the column `customers.email` makes the copy fail,
  and a database without `customers` makes it fail too. The fixtures state the claims over every database whose
  catalog is the guide's schema (a site).
- (c) `requireName` does not stop when `PRAGMA foreign_key_check` reports rows: the pragma returns them as rows, and
  the commit goes on. The replay `dangling` (a session of customer 99) and the replay `without-name` show it on
  pinned SQLite and in the model. A migration that must stop has to check the rows itself.

## Generalization analysis (per statement)

Implementation of the step laws (2026-10-27). All new modules are in
`packages/belay-sqlite-model/Belay/Sqlite/Model/`, imported from `Model.lean`.

- Table by name: `Database.tableNamed` (`TableByName.lean`) gives the position and the table that a
  name finds. `tableNamed_drop_kept` and `tableNamed_createTable` move it across a drop and a create.
- CREATE TABLE (`CreateTableStepLaws.lean`, `OrdinaryStepEffects.lean`). General form: any statement
  `CREATE TABLE name definition` that resolves to a `.createTable` effect and a continued step. The
  statement that SQLite refuses resolves to a prepare error (`SchemaFailureLaws.lean`,
  `resolveCreateTable_form`), which has the output `error 1`, keeps the connection and continues the
  step. A statement that resolves to a `.createTable` effect has no error: the effect errors have the reason
  `unmodeled`, and an `unmodeled` output ends the run (`Output.ofStep`). Failure law:
  `runScriptStep_createTable_failed` (a continued step with an error output has no further execution and
  the next connection is the connection). Success law: the next database is the database with the new
  catalog entry and an empty row list. Frame law: by name, any table keeps its position and rows. Left
  specific: nothing.
- DROP TABLE (`DropTableResolution.lean`, `DropTableStepLaws.lean`). General form: any drop. With
  foreign keys off (`rules = none`) the drop never fails and the next database is `database.drop positions`.
  Frame law premise: `connection.foreignKeys = false` (which excludes cascades) and different folded
  names. A drop that SQLite refuses with foreign keys off resolves to a prepare error and keeps the
  connection (`runScriptStep_dropTable_off_failed`). With rules (foreign keys on, or trigger
  programs) the next database is the success of `dropKeys` and the catalog is
  `catalog.drop positions`. The failure law for this case has the explicit premise `noStop` (the key run has no `constraintFail` or `constraintRollback` error), because
  stop-freedom from an empty program list needs an induction through the row engine. Open point: derive
  `noStop` from `programs = []`.
- Pragmas (`PragmaStepLaws.lean`, `ControlStepFrames.lean`). General form: every read-only pragma keeps
  the connection (`runScriptStep_pragma_keeps`, which covers `foreign_key_check`); `foreign_keys`
  setting changes only the enforcement flag, and only outside a transaction. Frame: database equality.
- BEGIN, COMMIT (`ControlStepLaws.lean`): idle BEGIN and active COMMIT are the transitions; BEGIN in
  a transaction and COMMIT outside one are continued steps with an error output that keep the
  connection. Frame: database equality (`ControlStepFrames.lean`).
- Rename (`RewriteStepLaws.lean`): a rename changes the catalog and keeps the rows; the guide's rebuild
  needs it.
- Read certificates by name (`CertifiedQueryOutputs.lean`, `ReadCertificate.lean`,
  `CertifiedQueryCommutation.lean`, `ReadCertificatePreservation.lean`, `DerivedColumnOutputs.lean`). The
  single-position form is replaced. `runScriptStep_simpleTable_output_append` takes a name, the position of
  the table found in the database before and the position found in the database after, with the
  resolution of the statement at each position. `ReadCertificate.Obligations` has the fields
  `resolvesOriginal` and `appended`; `appended` names the table, finds it in the second connection at a
  position that may differ, and resolves the statement moved to that position
  (`ReadCertificate.moved`). Callers moved: `DerivedColumnOutputs`, `ReadCertificate`,
  `CertifiedQueryCommutation`, `ReadCertificatePreservation` and the fixtures
  `S6RulesQueryPattern`, `S6RulesNegativeReads` (10 files estimated, 7 touched).
- Translation over several end states (`MigrationPatternAfter.lean`):
  `Migration.translatesAt_of_observations` now takes, for each execution of the migration, its own
  reached connection and output count, as a statement over branches. The caller
  `DerivedColumnQueries.translatesAt_of_outputs` derives the one-connection form from its uniform-branch
  fact. General form: yes, the premises that fixed one connection and one count are removed.
- INSERT SELECT success law (`UpsertInserted.lean`, `UpsertInsertedReady.lean`, `InsertSelectSuccess.lean`,
  `PlainScanProductions.lean`, `InsertSelectStepLaws.lean`). General form: any target table, any
  clauses (a row with no key conflict reaches no clause), any `RETURNING`, any conflict algorithm, any
  query whose productions are one certain production with no failure. The premises are exactly the ones
  the proof uses: `InsertFits` (alias cells, stored form, NOT NULL, STRICT types, CHECK, distinct keys,
  distinct bounded rowids, all on the table with the rows appended), the clause columns exist, the
  subqueries are plain, the fixed cells and `RETURNING` cannot fail, and the transfer rowids agree. The law is
  proved for statements without rules (`rules = none`: no trigger, and no foreign-key check). Left
  specific: the case with rules (foreign-key enforcement on, or triggers) needs an induction through the
  row engine (`insertKeys`) and is not covered. It is an open point for the coordinator. The law says
  nothing about the counts of the run. `Query.productions_scan` gives the productions of a simple
  query of the first source of one table, for every quiet context, with two restrictions: the query has no
  fallible call, and its condition has no `OR` when the table has several access orders.
  `productions_scan_single` gives the certain case when the table has one access order.
- Fixtures (`tests/surface/SchemaStepLaws.lean` and the modules after it). Kernel examples of each new law
  on concrete databases: failure laws of CREATE TABLE and DROP TABLE; the frame law of DROP TABLE with
  foreign keys off (the child is found by name at position 0 with its three rows); DROP TABLE with foreign
  keys on, whose cascade empties the child, so the frame law needs its premise; BEGIN, COMMIT and the
  pragmas on both sides of a transaction; a read certificate that survives the drop of an earlier table;
  the success law of INSERT from a query and four failing cases, one for each of NOT NULL, a duplicate
  key, CHECK and a STRICT type, each with the constraint error 19 from the model and with the field of
  `InsertFits` that fails. The native check runs four scripts on pinned SQLite 3.51.0 and compares rows and
  refusals with the model.
