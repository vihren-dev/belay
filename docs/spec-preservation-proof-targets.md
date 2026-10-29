# Preservation proofs: generalization and ownership inventory

Date: 2026-10-27. Status: foundation, API and execution-condition source migrations await acceptance.
Audience: designers and reviewers.
Contract: [ADR 0025 D2–D4](adr-0025-compositional-preservation-proofs.md).
Companion: [API removals and callers](spec-preservation-api-targets.md).

Names were checked against production revision `3e2212ed6983` on 2026-10-28. All declarations
below belong to `Belay.Sqlite.Model`. Owners were updated during the 2026-10-28 implementation. Removed declarations
are named as baseline targets; linked files are current owners. Future placement is constrained by imports; these lists do not require
one new module per group. Retained evidence can move without changing its claim.

## Move shared definitions and facts below their instances

| Current file | Definitions, fields or facts | Intended boundary |
| --- | --- | --- |
| [TableAtomFrames][frame] and [EffectSatisfies][effect] | `Database.EachTable`; `Effect.Satisfies`; `Effect.satisfies_of_effectDatabase`; `Effect.satisfies_of_database` | General quantification and success/carried-FAIL preservation now sit below `RowLocalAtoms` and key instances. |
| [TableAtomFrames][frame] | `TableAtom` and fields `empty`, `sublist`, `renamed`, `dropped`; `Database.EachTable.appendEmpty` | The shared contract is below `RowLocalAtom`; atom-specific frames and instances remain above it. |
| [RowLocalAtoms][atoms] | `RowLocalAtom.toTableAtom`, `.constraints`; `RowLocalAtom.facts` | Share empty/sublist/rename/drop facts with `TableAtom`, and keep the independent constraint implication. Inheritance now supplies the four frame fields without a second implementation. |
| [RowEngineFacts][engine-facts] | `Database.Every`, `Database.Every.setRows` | Expose the catalog/position-dependent update primitive below both table-local and key instances; keep its out-of-range row-list behavior. |
| [TableAtomWrites][table-writes] | `checkedWrite_satisfies`, `insertOutcome_satisfies` | General checked-write/insert facts now serve `RowLocalWrites` without a reverse import. |
| [RunHoldsStep][step] | `SqlState.Holds`, `Outcome.Holds`, `SqlTransition.Holds` | General state/outcome predicates remain below per-atom run evidence; move only as needed to break specialization imports. |
| [EffectSatisfies][effect] | `Effect.satisfies_and` | The existing four-way conjunction evidence now lives with the generic effect facts. |

The former reverse paths through `RowLocalFrame` and `RowLocalWrites` are removed.
`RowLocalFrame` is deleted. `Database.table_append_cases` also moved from
`KeysUniqueCreate` to the general frame owner, removing the remaining key-instance import.

## Replace duplicated update proofs with generic applications

| Current file and declaration | Replacement proof source | Preserve |
| --- | --- | --- |
| [TableAtomFrames][frame]: `Database.EachTable.setRows` | `Database.Every.setRows`, ignoring catalog/position | No extra `RowsShaped` assumption. |
| [KeysUniqueFrame](../packages/belay-sqlite-model/Belay/Sqlite/Model/KeysUniqueFrame.lean): `Database.KeysUnique.setRows` | `Database.Every.setRows`, using catalog-selected keys | Selection depends on catalog and table position. |
| Removed `checkedWrite_rowLocal` | `checkedWrite_satisfies` and `RowLocalAtom.constraints` | Success and carried constraint FAIL. |
| Removed `insertOutcome_rowLocal` | `insertOutcome_satisfies` and `RowLocalAtom.constraints` | Same shape and original write assumptions. |
| Removed `Database.EachTable.append` | `Database.EachTable.appendEmpty` with the shared table contract | Original empty-table assumptions. |

The first four have historical replacement proofs in
[DispatchPrimitives](../experiments/proof-simplification/DispatchPrimitives.lean).
The implementation uses the general primitives and removes the two row-local
write wrappers. Append callers now pass the inherited table contract directly.
Current acceptance and temporary witness retirement are recorded in the
[foundations status](../plans/20261026-preservation-foundations.status.md). These counts do not add
to the 84 endpoint deletion count as measured savings.

## Consolidate complete statement dispatches

| Current file | Target declaration | Intended change |
| --- | --- | --- |
| [AdmittedTableAtomStatement][dispatch] | `runStatement_tableAtom` | Own the single complete constructor dispatch for these table-atom families. |
| [RowLocalStatement](../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalStatement.lean) | `runStatement_rowLocal` | Derive from that dispatch using row-local constraints, ADD/DROP COLUMN, INSERT-query and write evidence. |
| [AdmittedDistinctStatement](../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedDistinctStatement.lean) | `runStatement_rowidsDistinct` | Derive from that dispatch using distinct-rowid evidence. |

Retain the independent leaf evidence used by those applications:

- [RowLocalAtoms][atoms]: `Table.notNullAtom`, `Table.typesFitAtom`,
  `Table.checksHoldAtom`, and the three table frame lemmas.
- [AdmittedAtomFrames][atom-frames]: `Table.rowidsDistinctAtom`,
  `Table.rowidsInRangeAtom`, `Table.rowsWideAtom`, `Table.rowsStoredAtom`,
  `Table.rowsAliasedAtom` and their frame lemmas.
- [RowEngineFacts][engine-facts]: `TableFacts`, `WriteLaws`, `TableFacts.laws`.
- [AdmittedPlainWrites][plain]: `passed_rowidsDistinct`; [TableAtomWrites][table-writes]
  owns the generic `runStatement_insert_atom`, `runStatement_update_atom`,
  `runStatement_delete_tableAtom` operation facts.
- [AdmittedSchemaStatements](../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedSchemaStatements.lean):
  `runStatement_create_tableAtom`; [RowLocalSchema](../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalSchema.lean):
  `Database.EachTable.drop`, `runStatement_drop_rowLocal`.
- [RowLocalAddColumnTheorems](../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalAddColumnTheorems.lean):
  the generic ADD COLUMN fact and distinct atom extension facts listed in the
  companion inventory. Placement changes may be needed to remove wrapper imports.
- [StatementRewrite](../packages/belay-sqlite-model/Belay/Sqlite/Model/StatementRewrite.lean):
  `runStatement_rewrite_satisfies` and
  `runStatement_rewrite_tableAtom` supply rename evidence with unchanged rows
  and equal `blankNames` shapes. `runStatement_rewrite_satisfies` now assumes
  only outline equality; FK selection equality must come from its caller.
- [StatementDropColumn](../packages/belay-sqlite-model/Belay/Sqlite/Model/StatementDropColumn.lean):
  `runStatement_dropColumn_satisfies`, `runStatement_dropColumn_eachTable`
  use the execution guard and the independent `dropped`/`renamed` evidence.
  The shared `dropped` field requires `CatalogTable.DropsCleanly index` and
  yields the atom of `Table.dropColumn index`. Retain its distinct supporting
  facts in `DropColumnFactLaws` and `DropColumnAdmittedLaws`; do not add
  `Database.Valid`, `RowsShaped` or readiness to the whole-statement formulas.
- [InsertSelectLaws](../packages/belay-sqlite-model/Belay/Sqlite/Model/InsertSelectLaws.lean):
  `runStatement_insertSelect_none_satisfies`; [InsertSelectOutcomeLaws](../packages/belay-sqlite-model/Belay/Sqlite/Model/InsertSelectOutcomeLaws.lean):
  `runStatement_insertSelect_some_satisfies` supply the dispatch's `selects`
  premise and rule-bearing case. Preserve source failures, upsert behavior
  and carried constraint FAIL.

Leaf wrappers with no remaining purpose can disappear after caller migration;
the required initial targets are the complete dispatches and four checked
primitive replacements. `runStatement_keysUnique` and FK statement/engine
dispatches are outside this table-atom consolidation.

## Generalize condition propositions and share run inductions

| Current file | Exact target declarations | Intended change |
| --- | --- | --- |
| [RunHolds][raw] | `StatementKeeps`, `RunConditionsWith` | Conditions inspect actual clock, visible counters, parameters, resolved statement and database; preservation still covers every member of `StatementRun.effects`. |
| [RunHolds][raw] | `advance_holds`, `runSqlFrom_holds`, `runSql_holds`; `RunConditionsWith.of_unconditioned` | One raw induction and its entry/condition laws use the richer condition. |
| Removed `RunHoldsReady` | `StatementKeepsReady`, `StatementKeeps.toReady`, `advance_holds_ready`, `runSqlFrom_holds_ready`, `runSql_holds_ready` | These names and their parallel traversal are deleted. Readiness is part of the common condition in [RunHolds][raw]. |
| [RunHolds][raw] | `StatementKeeps.and`, `RunConditionsWith.always`, `RunConditionsWith.with_ready`, `SqlState.Holds.mono` | Unified conjunction, unconditional conditions, supported-run readiness and state monotonicity. |
| [ScriptConditions](../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptConditions.lean) | `ScriptStepCondition`, `ScriptConditionsWith`, `.of_invariant` | Guarded conditions follow every reached execution's next connection, selected clock, counters and database. Invariant-derived obligations use the same traversal. |
| [ScriptRunHolds][surface] | `runScriptStep_holds`, `runScriptAllFrom_holds`, `runScriptFrom_holds` | One continuing-step proof and all-execution surface induction; derive the canonical-run result by membership. |
| [ScriptRunDerived][derived] | `runScriptAllFrom_holds_derived`, `runScriptFrom_holds_derived` | Thin applications of the shared proof; the old `runScriptStep_holds_ready` and repeated preservation inductions are deleted. |
| [InsertSelectKeeps](../packages/belay-sqlite-model/Belay/Sqlite/Model/InsertSelectKeeps.lean) | `StatementKeeps.ofOwnRun` | The unified bridge retains INSERT-query-to-upsert condition compatibility at the actual inputs, including the selected execution's readiness implication. The ready-only bridge is deleted. |

Keep these transport facts, adapting only their applications/imports:
[RunHoldsStep][step] `SqlState.finish_holds`, `SqlState.failed_holds`,
`SqlState.publish_holds`, `advanceWith_holds`, `SqlTransition.counted_holds`;
[ScriptRunHolds][surface] `Connection.afterStep_holds`.

The actual inputs come from [SqlAdvance](../packages/belay-sqlite-model/Belay/Sqlite/Model/SqlAdvance.lean)
and [StatementStep](../packages/belay-sqlite-model/Belay/Sqlite/Model/StatementStep.lean).
Their executable behavior is unchanged. Ordinary runs use `initial := none`;
state readiness includes counter knowledge beyond raw evaluator readiness.
Surface runs use `statementClock`. Conditions follow reached states, with the
halt/ended and discarded-error behavior specified in ADR 0025 D4.
`runScriptFrom_mem_runScriptAllFrom` in [ScriptRunAll](../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunAll.lean)
already supplies canonical-run membership. Migrate `ScriptRunSingleton`'s
condition clients too. Do not infer an input-dependent upsert condition merely
from the INSERT-query condition: preserve an explicit compatibility premise,
including the readiness implication when needed. `ExecutionCounters`'s
counter-knowledge relations remain distinct evidence, not deletion targets.

## Migrate invariant certificates and resolver bridges

These certificates remain independent evidence, adjusted to the common condition
interface. The listed propositions keep their meanings and distinct premises.

| Current owner | Exact declarations |
| --- | --- |
| [ValidAtomsRuns](../packages/belay-sqlite-model/Belay/Sqlite/Model/ValidAtomsRuns.lean) | `notNull_statementKeeps`, `typesFit_statementKeeps`, `checksHold_statementKeeps` |
| [KeysUniqueRuns](../packages/belay-sqlite-model/Belay/Sqlite/Model/KeysUniqueRuns.lean) | `keysUnique_statementKeeps` |
| [ValidAtomsTogether](../packages/belay-sqlite-model/Belay/Sqlite/Model/ValidAtomsTogether.lean) | `constraintAtoms_statementKeeps` |
| [AdmittedStatementKeeps][admitted] | `catalogSupported_statementKeeps`, `rowsShaped_statementKeeps`, `rowidsDistinct_statementKeeps`, `rowidsInRange_statementKeeps`, `rowsWide_statementKeeps`, `rowsStored_statementKeeps`, `rowsAliased_statementKeeps`, `admitted_statementKeeps` |
| [AdmittedStatementKeeps][admitted] | Retain propositions `Database.CatalogSupported`, `Database.RowsStoredWide`, `Database.RowsAliasedSupported`, `Resolved.Statement.AppliedValid`. |
| [ForeignKeyRuns](../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeyRuns.lean) | `rowReferences_statementKeeps`, `foreignKeyAtoms_statementKeeps` |
| [ForeignKeySchemaRuns](../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeySchemaRuns.lean) | `parentSchemasCompatibleKeeps` |
| [ForeignKeySelectedRuns](../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeySelectedRuns.lean) | `parentSchemasCompatibleSelectedKeeps`, `foreignKeyAtomsSelected_statementKeeps` |
| [AtomsConditionsOfLink](../packages/belay-sqlite-model/Belay/Sqlite/Model/AtomsConditionsOfLink.lean) | `Resolved.Statement.runCondition_of_link`, `.notNullCondition_of_admitted`, `.typesFitCondition_of_link`, `.checksHoldCondition_of_admitted`, `.atomsCondition_of_link` |

The resolver bridge formulas stay available; adjust their use in
`runScriptAllFrom_admittedWith` instead of repeating resolution reasoning at clients.
Catalog validity, row shape and distinct-rowid certificates now omit their unused
readiness premise. Range, width, stored rows, row aliases and the combined
admission certificate retain raw readiness in the condition.
No FK schema/row atom, mapping selection or work condition is collapsed merely
because the run-lifting contract becomes shared.
Latest FK rename conditions require `renamed.selectedParents =
database.catalog.selectedParents`; `sameOutline` alone is insufficient.
DROP COLUMN uses its own execution guard and remains unconditional in those
conditions. Retain these current meanings in all migrated certificates.

## Acceptance and test lifetime

Use the companion's caller/test list and the [foundations task](../plans/20261026-preservation-foundations.task.md)
and [condition task](../plans/20261026-preservation-context.task.md) for acceptance.
`admitted_atoms_statement_theorems_test.py` checks independent atom claims;
retain meaningful premise coverage when dispatch bodies change. The complete
current-formula adapters, four primitive probes and import/count comparisons remain
temporary acceptance work. Keep one copy through the final contract change,
record Nix acceptance against `3e2212ed6983`'s claims, then remove redundancy.
Historical prototypes predate rename, DROP COLUMN and alternative INSERT-query execution;
their previous successful builds do not validate the changed contracts.
These inventories are review guides, not permanent CI manifests or promised
net source/build savings.

[frame]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TableAtomFrames.lean
[effect]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/EffectSatisfies.lean
[table-writes]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TableAtomWrites.lean
[atom-frames]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedAtomFrames.lean
[atoms]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalAtoms.lean
[engine-facts]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowEngineFacts.lean
[plain]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedPlainWrites.lean
[writes]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalWrites.lean
[step]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RunHoldsStep.lean
[dispatch]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedTableAtomStatement.lean
[raw]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RunHolds.lean
[surface]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunHolds.lean
[derived]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunDerived.lean
[admitted]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedStatementKeeps.lean
