# Status: derived-column migration laws

Created 2026-10-27. Status: OPEN.
Task: [task file](20261027-derived-column-laws.task.md).
Specs: ADR 0017 S6 and S8; the S6 automation task and its part 2 open point 5;
the migration-patterns status section "Owner decision on the example modules
(2026-10-26)".

## Decisions

- 2026-10-26 (owner): the general content of the `NormalizedField*` modules
  stays under general names; the plan, the lookup simulation and the expansion
  theorem move to `tests/surface`.
- 2026-10-27 (owner): each new or kept statement is as general as the proof
  allows at a reasonable cost.
- 2026-10-27 (coordinator): the universal migration query claim over a site
  (S6 part 2 open point 5) is part of this task.

## Map of the 16 modules at the task base (read-only survey, 2026-10-27)

M = `packages/belay-sqlite-model/Belay/Sqlite/Model/`, S =
`packages/belay/Belay/Sqlite/`. No declaration names a guide table or fixes SQL
text. "lower" marks laws that fix the derived expression to `lower` of one
source column (of any affinity), stored in an appended TEXT column.

- M/NormalizedFieldRows: `store_lower`, `comparisonOperands_lower`,
  `eval_lower`, `assign_lower_append`, `updated_lower_append` (lower);
  `generatedCells_plain`, `movedRowid_append` (general; `PlainInsertRows.lean`
  uses `generatedCells_plain`).
- M/NormalizedFieldQueries: `originalFilter`, `storedFilter`,
  `*_append`, `results_translate`, `results_preserve` (lower). The private
  `simple_results_append` is general content: any two conditions that agree on
  each old row and its extended row give the same results, also when the new
  condition reads the appended cells. `Query.simple_results_append` does not
  cover that case (it needs a condition that reads below the old width).
- M/NormalizedFieldScan: private stable-sort-commutes-with-map lemmas
  (general content, no counterpart elsewhere); `sourceRows_updated_lower`.
- M/NormalizedFieldEffects: `Model.runStatement_update_ok`,
  `Model.table_after_update_ok` (general; `PlainUpdateEffect.lean` uses them);
  `table_after_lower_update`, `sourceRows_after_lower_update` (lower).
- M/NormalizedFieldResolution: `textDefinition`, `textColumn`,
  `addColumn_resolution_cases`, `columnPosition_append`, `columnPosition_new`,
  `findTable_addColumn` (general; compare `Catalog.findTable_addColumn` in
  `CatalogAddColumnSearch.lean`); `resolve_lower_column*` (lower).
- M/NormalizedFieldUpdateResolution: `update_resolution`,
  `backfill_programs_empty`, `withWrite_backfill`, `backfill_resolution`
  (lower).
- M/NormalizedFieldDdlEffects: `add_step` (general for a plain TEXT column;
  compare `addColumn_database` in `AddColumnEffect.lean`), `trigger_step`
  (general).
- M/NormalizedFieldBackfillStep: `loweredRows`, `backfill_step` (lower).
- M/NormalizedFieldExpansion: `expansionScript`, `withTrigger`,
  `expandedDatabase`, `expansion_state` (the guide's script).
- M/NormalizedFieldSelectResolution: `findPosition_append_rejected`,
  `findTable_createTrigger`, `resolveColumns_identifier(_at)` (general;
  `GlobalSignupInvariant.lean` uses `resolveColumns_identifier_at`);
  `resolve_lower_parameter`, `resolve_original_filter*`,
  `resolve_stored_filter*` (lower).
- M/NormalizedFieldLookups: `originalLookup`, `storedLookup`,
  `resolve_original_lookup`, `resolve_stored_lookup` (lower);
  `resolveStatement_select_column`, `originalFilter_calm`, `storedFilter_calm`,
  `simpleColumn_calm` (general or nearly general).
- M/NormalizedFieldExpandedTable: `expandedTable` and its lookups (the guide's
  script).
- M/NormalizedFieldLookupOutputs: `results_names`,
  `step_output_of_simple_query` (general); `translate_step_outputs`,
  `preserve_step_outputs` (the guide's script).
- S/NormalizedFieldExpansion: `expansion`, the lookup scripts, `Site`,
  `translatesAt_of_outputs`, `queryTranslates`, `queryPreserves`.
- S/NormalizedFieldPlan: `Plan`, `Plan.Source` and their laws.
- S/NormalizedFieldLookupSimulation: `Plan.lookup_steps`, `Plan.pairing`,
  `Plan.Related`, `Plan.scoped`, `Plan.lookups_agree_after_expansion` and
  others.
- Outside the 16: `S/SendSuccessIfOk.lean` `ifOk_send_expansion` (namespace
  `NormalizedFieldExpansion`).

Consumers in `tests/surface`: `NormalizedFieldLaws.lean` (23 axiom reports),
`NormalizedFieldExpansionLaws.lean` (8), `ApplicationExpansion.lean`,
`ApplicationCounterCalls.lean`, `ApplicationMissingTrigger.lean`,
`ExpansionCountClaims.lean`, `ExpansionCountQueries.lean`,
`GlobalSignupInvariant.lean`. Drivers: `tests/surface_migration_examples_test.py`,
`tests/surface_application_test.py`, `tests/surface_assertion_examples_test.py`
(all in the `surface` suite of `tests/nix_suites.json`).

## What each old module became (2026-10-27)

All 13 model and 3 belay `NormalizedField*` modules are deleted. No alias remains. `grep NormalizedField
packages/` finds nothing.

- Rows (`NormalizedFieldRows`): `assign_derived_append`, `updated_derived_append` (M/DerivedColumnRows) take any
  derived expression. `generatedCells_plain` is in M/AdmittedCellLaws, `movedRowid_append` in
  M/AdmittedUpdateRows. The lowercase facts `store_lower`, `comparisonOperands_lower`, `eval_lower` are in
  `tests/surface/LowercaseFilters.lean`.
- Queries (`NormalizedFieldQueries`): the general agreement lemma is `Query.simple_results_agree` and
  `Query.simple_results_append` in M/SimpleQueryAppend. `originalFilter`, `storedFilter`, `results_translate`,
  `results_preserve` are in `LowercaseFilters`.
- Scan (`NormalizedFieldScan`): `stableSort_map`, `Table.scanRows_map`, `sourceRows_map` in M/ScanRowMap;
  `sourceRows_updated_derived` in M/DerivedColumnBackfill.
- Effects: `runStatement_update_ok`, `table_after_update_ok` stayed in M/PlainUpdateEffect (their only
  consumer was there); `table_after_derived_update`, `sourceRows_after_derived_update` in
  M/DerivedColumnBackfill.
- Resolution: `columnPosition_append(_new)` in M/ColumnPositionAppend, `addColumn_resolution_cases`,
  `addColumn_plain_step` in M/AddColumnPlainStep, `backfill_resolution` and its parts in
  M/BackfillUpdateResolution and M/BackfillStatementResolution (any assigned expression that mentions a
  column), `resolveStatement_select_column` and `resolveColumns_identifier_at` in M/SelectColumnResolution,
  `findPosition_append_rejected`, `Catalog.findTable_createTrigger` in M/CatalogTriggerSearch,
  `createTrigger_step` in M/CreateTriggerStep, `Statement.simpleTable_calm` in M/SimpleTableCalm,
  `runScriptStep_next_of_database` in M/ScriptStepDatabase, `Expr.reindex_id` in M/Resolution/SyntaxReindexLaws.
  Lowercase resolution (`resolve_lower_*`, the two lookups) is in `tests/surface/LowercaseLookups.lean`;
  `textDefinition` is in `LowercaseFilters`.
- Script and outputs: `derivedColumnScript`, `derivedColumn_state` (M/DerivedColumnScript),
  `Database.addDerivedColumn` and its table laws (M/DerivedColumnTable), `derivedColumn_lookup_outputs`,
  `derivedColumn_preserved_outputs` (M/DerivedColumnOutputs), `runScriptStep_simpleTable_output(_agree,
  _append)` (M/CertifiedQueryOutputs).
- Belay: `DerivedColumnMigration` (`migration`, `Site`, `reached`), `DerivedColumnReads`
  (`Site.LookupMove`, `Site.ReadPreserved` and their output theorems), `DerivedColumnQueries`
  (`translatesAt_of_outputs`, `queryTranslates`, `queryPreserves`, over any domain predicate).
  `SendSuccessIfOk.ifOk_send_expansion` became `ifOk_send_derivedColumn`.
- Fixtures: the guide's expansion script, plan, lookup simulation and theorem are now the `Lowercase*`
  modules in `tests/surface` (`LowercaseFilters`, `LowercaseLookups`, `LowercaseExpansion`, `LowercaseQueries`,
  `LowercasePlan`, `LowercaseSimulation`), each proved from the general laws, with no axiom report.

## Generalization analysis (owner rule: generalize every new statement)

General form chosen, and what stays specific:

- Row, scan, backfill and effect laws (M/DerivedColumnRows, DerivedColumnBackfill, DerivedColumnBackfillStep,
  DerivedColumnTable, DerivedColumnScript, DerivedColumnOutputs): any table, any derived expression that
  reads only old columns and is context-free, any assigned column definition. Premises are those of the
  proofs (wide and aliased rows, key positions inside the columns, plain columns). Nothing stays specific.
- Resolution laws (M/BackfillUpdateResolution, M/SelectColumnResolution, ...): any written expression
  that mentions the new column's source columns only through `assignedExpression`; any column name. A
  resolution of the written expression itself is a premise, because it depends on the expression.
- `DerivedColumnMigration.Site`: any table name, definition and written expression. `LookupMove` and
  `ReadPreserved`: any pair of simple-table reads whose filters agree on every row; they do not mention
  `lower` or comparisons. The filter agreement is a premise, since it holds only for particular
  expressions.
- `queryTranslates`, `queryPreserves`: any domain predicate and any site selector. Stay specific: only simple
  one-table reads (no joins, no subqueries); the general model has no closed form for the output of
  other queries.
- `Lowercase*` fixtures: `TextFieldSite` is general in table, id, stored column; `LowercaseSite` and
  the lookups stay specific to `lower` of one column, because they are the guide's example.
  `S6ColumnLookups`: `columnPreserved` holds for any declared type and collation of the read column.
- `S6RulesQuerySites.lookup_preserved_at_every_site`: every valid database with the site, every bound
  value, every complete environment where the migration succeeds. Left specific: the table and column
  names (`items`, `name`) because the guide's statements name them. `lookup_commutes` of
  `S6RulesQueryPattern` is NOT generalized: commutation needs the admissibility closure of the migrated
  database and the obligations over the migrated connection, which is more work than preservation, and the
  task makes it optional.
- `ConcatFilters`, `ConcatExpansion`: the same shape for `a || b`; `ConcatSite` is general in table and
  columns, with general trigger and bound-value lists. The facts specific to concatenation
  (`store_pipes`, `pipesFilter` laws) are proved here.
- `DerivedColumnExamples`: concrete databases, on purpose; they show the site is satisfiable and that the
  affinity premise fails (`a + b` stored in TEXT, probe 5.0).

## Axiom reports

Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`. Counts: `NormalizedFieldLaws` 23 (kept),
`NormalizedFieldExpansionLaws` 8 (kept), `ExpansionCountClaims` 3 (kept), `MigrationExpansionCounter` 7
(unchanged), Application fixtures unchanged. New: `S6RulesQuerySites` 6, `DerivedColumnExamples` 9. The six
`Lowercase*` and the two `Concat*`/`S6ColumnLookups` library modules have 0 reports (library modules; the
checks are in their consumers). The old `NormalizedFieldExpansionLaws` reports on `expansion` theorems now
name `DerivedColumnMigration.translatesAt_of_outputs`, `LowercaseFixture.queryTranslates/queryPreserves`
and `Model.derivedColumn_state`; their number is unchanged.

## Kernel examples and native checks

`tests/surface_derived_column_test.py`: the universal site claim chain, and the examples chain with native
SQLite 3.51.0 replays. Examples: concat `a || b` into TEXT (lookup translates), and `a + b` into TEXT with the
probe 5.0 (before `[[1]]`, after `[]`, in the model and in native SQLite).

## Guide change to record (private guide, not edited here)

The guide's expansion script, plan, lookup simulation and expansion theorem are no longer library modules.
Their references move from `Belay.Sqlite.NormalizedField*` to `tests/surface/Lowercase*.lean`; the guide text
that names `ifOk_send_expansion` becomes `ifOk_send_derivedColumn`; the migration query claim may cite
`tests/surface/S6RulesQuerySites.lean` (`lookup_preserved_at_every_site`).

## Progress

- 2026-10-27: task specified on top of the NOT IN task (PR #281). Table rebuild part 3 touches none
  of the 16 modules or their fixtures; it shares the model barrel and lakefile. The branch merges part 3
  before its final gates.
- 2026-10-27: spec reviews `20261027T093454Z-a5ba83bf` (1 must: the survey called the private
  filter-agreement lemma a specialization; 1 should: the source column is of any affinity; both fixed
  in the next commit) and `20261027T093610Z-530aa0f2` (no findings).
- 2026-10-27: review `20261027T093743Z-84c09111` (1 should: part 3 shares the model barrel and
  lakefile; fixed in the next commit).
- 2026-10-27: review `20261027T093842Z-bcc1caa1` (no findings).
- 2026-10-27: commit `dbb25391`: general laws, deletion of the `NormalizedField*` modules, the `Lowercase*`
  fixtures and the driver changes. Nix results: see the end-of-task gates.
- 2026-10-27: commit `593d6f21`: the universal claim, the kernel examples and the new driver
  `tests/surface_derived_column_test.py` (in `surfaceChecks` of `tests/nix_suites.json`). Nix results: see the end-of-task gates.
- 2026-10-27: review `20261027T110912Z-dbb25391` of `dbb25391`: finding 1 (R19, the status file named files
  of the next commit) is a commit boundary and was rejected; findings 2 and 3 (R2, plain-words statements of
  `Expr.eval_compare_stored_left` and `sourceRows_addDerivedColumn`) were fixed in a `refactor:` commit.
- 2026-10-27: review `20261027T111149Z-593d6f21` of `593d6f21`: finding 1 (R11, the new driver imports
  `tests/surface_assertion_examples_test.py`, which the inputs of `surfaceChecks` lacked) is fixed by adding
  the module to the shared inputs in `build-support/tests.nix`; finding 2 (R19) and finding 3 (R19, local
  results in the status file) are fixed by this wording.
- 2026-10-27: review `20261027T111227Z-7a296e38` of the first `refactor:` commit: the example of when the
  premise `agree` holds was too weak (BLOB affinity); the example is deleted.
- 2026-10-27: merged `tasks/table-rebuild-part3` (PR #282, `b7ec539c`) as the change `merge: table rebuild
  part 3 into the derived-column laws`. The only textual conflict was the model `lakefile.toml` glob list
  (union of both sides, with the 13 removed `NormalizedField*` modules dropped). The barrels merged without
  conflict. Part 3's new resolved statement constructor `.dropColumn` needed no change in the new modules.

## End-of-task Nix checks (on the merged tree, change `merge: table rebuild part 3 ...`)

- `just dev-build`: passes on the merged tree.
- `just test-full`: passes, `/nix/store/k67m18r5lk2r8qkc51px335xcy9yif59-sqlite-verifier-test-reports`. Suite times
  (limit 1200 s): `surface` 1039 s with 407 tests
  (`/nix/store/25gvpf1q5arvqmlnpc7znawj2025b6mc-sqlite-verifier-test-surface-1`), `surfaceChecks` 939 s with 43
  tests (`/nix/store/inivfhgbca7yc37ajmp3li88mc6i91bq-sqlite-verifier-test-surfaceChecks-1`). Two earlier runs on the
  same tree failed only by timeout (the recipe at 1500 s, then the `surface` suite at 1200 s) while two other
  `test-full` runs shared the machine; no test failed. The new driver
  `tests/surface_derived_column_test.py` takes about 25 s.
- `just verdict`: passes, `/nix/store/7mrg2ndl2h7nqnb81ms2njwpic17s8wk-sqlite-verifier-verdict`; the model
  predictions agree with the baseline before this work (checked earlier on the unmerged tree: 55 files, byte-identical).
- `just test-nix`: 71 passed.
- `just test-scheduled-checks`: passes, `/nix/store/5qq2c3cc09smhjp08qc3vvx7za05r62p-sqlite-verifier-scheduled-check-reports`.
