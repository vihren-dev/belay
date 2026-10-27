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

## Progress

- 2026-10-27: task specified on top of the NOT IN task (PR #281). The
  implementation starts on a base that contains table rebuild part 3.
