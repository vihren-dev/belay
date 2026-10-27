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
