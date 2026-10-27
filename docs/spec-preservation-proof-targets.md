# Preservation proofs: generalization and ownership inventory

Date: 2026-10-27. Status: PROPOSED; implementation targets, not completed changes.
Audience: designers and reviewers.
Contract: [ADR 0025 D2–D4](adr-0025-compositional-preservation-proofs.md).
Companion: [API removals and callers](spec-preservation-api-targets.md).

Names were checked against production revision `3fe5caef`. All declarations
below belong to `Belay.Sqlite.Model`. Current owners identify the source to
change. Future placement is constrained by imports; these lists do not require
one new module per group. Retained evidence can move without changing its claim.

## Move shared definitions and facts below their instances

| Current file | Definitions, fields or facts | Intended boundary |
| --- | --- | --- |
| [RowLocalFrame][frame] | `Database.EachTable`; `Effect.Satisfies`; `Effect.satisfies_of_effectDatabase`; `Effect.satisfies_of_database` | General table quantification and success/carried-FAIL preservation must be available without importing `RowLocalAtoms` or key instances. |
| [AdmittedAtomFrames][atom-frames] | `TableAtom` and fields `empty`, `sublist`; `Database.EachTable.appendEmpty` | Put the weakest table contract below `RowLocalAtom`; retain atom-specific frame lemmas/instances above it. |
| [RowLocalAtoms][atoms] | `RowLocalAtom.empty`, `.sublist`, `.constraints`; `RowLocalAtom.facts` | Share the first two facts with `TableAtom`, and keep the independent constraint implication. Use inheritance or a small projection; no second frame implementation. |
| [RowEngineFacts][engine-facts] | `Database.Every`, `Database.Every.setRows` | Expose the catalog/position-dependent update primitive below both table-local and key instances; keep its out-of-range row-list behavior. |
| [AdmittedPlainWrites][plain] | `checkedWrite_satisfies`, `insertOutcome_satisfies` | Make the general checked-write/insert facts usable by `RowLocalWrites` without the current reverse import. |
| [RunHoldsStep][step] | `SqlState.Holds`, `Outcome.Holds`, `SqlTransition.Holds` | General state/outcome predicates remain below per-atom run evidence; move only as needed to break specialization imports. |
| [ValidAtomsTogether](../packages/belay-sqlite-model/Belay/Sqlite/Model/ValidAtomsTogether.lean) | `Effect.satisfies_and` | Place shared conjunction evidence with the generic effect facts if used there; its four-way application need not define a new framework. |

The current reverse dependency paths are `AdmittedAtomFrames → RowLocalFrame →
RowLocalAtoms` and `AdmittedPlainWrites → RowLocalWrites`. Adding the opposite
imports would create cycles; generalization must first change ownership.

## Replace duplicated update proofs with generic applications

| Current file and declaration | Replacement proof source | Preserve |
| --- | --- | --- |
| [RowLocalFrame][frame]: `Database.EachTable.setRows` | `Database.Every.setRows`, ignoring catalog/position | No extra `RowsShaped` assumption. |
| [KeysUniqueFrame](../packages/belay-sqlite-model/Belay/Sqlite/Model/KeysUniqueFrame.lean): `Database.KeysUnique.setRows` | `Database.Every.setRows`, using catalog-selected keys | Selection depends on catalog and table position. |
| [RowLocalWrites][writes]: `checkedWrite_rowLocal` | `checkedWrite_satisfies` and `RowLocalAtom.constraints` | Success and carried constraint FAIL. |
| [RowLocalWrites][writes]: `insertOutcome_rowLocal` | `insertOutcome_satisfies` and `RowLocalAtom.constraints` | Same shape and original write assumptions. |
| [RowLocalFrame][frame]: `Database.EachTable.append` | `Database.EachTable.appendEmpty` with the shared table contract | Original empty-table assumptions. |

The first four are the experiment-checked replacement formulas in
[DispatchPrimitives](../experiments/proof-simplification/DispatchPrimitives.lean).
The append row is a consolidation candidate from the shared empty-table field;
verify its original formula during implementation. Delete replaced proof bodies
and unnecessary specializations after callers migrate. These counts do not add
to the 84 endpoint deletion count as measured savings.

## Consolidate complete statement dispatches

| Current file | Target declaration | Intended change |
| --- | --- | --- |
| [AdmittedTableAtomStatement][dispatch] | `runStatement_tableAtom` | Own the single complete constructor dispatch for these table-atom families. |
| [RowLocalStatement](../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalStatement.lean) | `runStatement_rowLocal` | Derive from that dispatch using row-local constraints, ADD COLUMN and write evidence. |
| [AdmittedDistinctStatement](../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedDistinctStatement.lean) | `runStatement_rowidsDistinct` | Derive from that dispatch using distinct-rowid evidence. |

Retain the independent leaf evidence used by those applications:

- [RowLocalAtoms][atoms]: `Table.notNullAtom`, `Table.typesFitAtom`,
  `Table.checksHoldAtom`, and the three table frame lemmas.
- [AdmittedAtomFrames][atom-frames]: `Table.rowidsDistinctAtom`,
  `Table.rowidsInRangeAtom`, `Table.rowsWideAtom`, `Table.rowsStoredAtom`,
  `Table.rowsAliasedAtom` and their frame lemmas.
- [RowEngineFacts][engine-facts]: `TableFacts`, `WriteLaws`, `TableFacts.laws`.
- [AdmittedPlainWrites][plain]: `passed_rowidsDistinct` and the generic
  `runStatement_insert_atom`, `runStatement_update_atom`,
  `runStatement_delete_tableAtom` operation facts.
- [AdmittedSchemaStatements](../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedSchemaStatements.lean):
  `runStatement_create_tableAtom`; [RowLocalSchema](../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalSchema.lean):
  `Database.EachTable.drop`, `runStatement_drop_rowLocal`.
- [RowLocalAddColumnTheorems](../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalAddColumnTheorems.lean):
  the generic ADD COLUMN fact and distinct atom extension facts listed in the
  companion inventory. Placement changes may be needed to remove wrapper imports.

Leaf wrappers with no remaining purpose can disappear after caller migration;
the required initial targets are the complete dispatches and four checked
primitive replacements. `runStatement_keysUnique` and FK statement/engine
dispatches are outside this table-atom consolidation.

## Generalize condition propositions and share run inductions

| Current file | Exact target declarations | Intended change |
| --- | --- | --- |
| [RunHolds][raw] | `StatementKeeps`, `RunConditionsWith` | Conditions inspect actual clock, visible counters, parameters, resolved statement and database. |
| [RunHolds][raw] | `advance_holds`, `runSqlFrom_holds`, `runSql_holds`; `RunConditionsWith.of_unconditioned` | One raw induction and its entry/condition laws use the richer condition. |
| [RunHoldsReady][ready] | `StatementKeepsReady`, `StatementKeeps.toReady`, `advance_holds_ready`, `runSqlFrom_holds_ready`, `runSql_holds_ready` | Replace the parallel contract/traversal with explicit readiness in the common condition; remove old production names after migration. |
| [RunHoldsReady][ready] | `StatementKeepsReady.and`, `RunConditionsWith.always`, `SqlState.Holds.mono` | Supply conjunction and unconditional-condition facts for the unified API; preserve generic state monotonicity. |
| [ScriptRunHolds][surface] | `ScriptConditionsWith`, `runScriptStep_holds`, `runScriptFrom_holds` | One continuing-step proof and surface induction with reached-input conditions. |
| [ScriptRunDerived][derived] | `runScriptStep_holds_ready`, `runScriptFrom_holds_derived` | Derive resolver/invariant obligations through the same proof, without another script induction or compatibility traversal. |

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
`runScriptFrom_admittedWith` instead of repeating resolution reasoning at clients.
Some certificates currently accept readiness that their body does not use;
do not add it as a necessary premise for an independently unconditional claim.
No FK schema/row atom, mapping selection or work condition is collapsed merely
because the run-lifting contract becomes shared.

## Acceptance and test lifetime

Use the companion's caller/test list and the [foundations task](../plans/20261026-preservation-foundations.task.md)
and [condition task](../plans/20261026-preservation-context.task.md) for acceptance.
`admitted_atoms_statement_theorems_test.py` checks independent atom claims;
retain meaningful premise coverage when dispatch bodies change. The complete
old-formula adapters, four primitive probes and import/count comparisons remain
temporary acceptance work. Keep one copy through the final contract change,
record Nix acceptance, then remove redundancy. These inventories are review
guides, not permanent CI manifests or promised net source/build savings.

[frame]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalFrame.lean
[atom-frames]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedAtomFrames.lean
[atoms]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalAtoms.lean
[engine-facts]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowEngineFacts.lean
[plain]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedPlainWrites.lean
[writes]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalWrites.lean
[step]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RunHoldsStep.lean
[dispatch]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedTableAtomStatement.lean
[raw]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RunHolds.lean
[ready]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RunHoldsReady.lean
[surface]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunHolds.lean
[derived]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunDerived.lean
[admitted]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedStatementKeeps.lean
