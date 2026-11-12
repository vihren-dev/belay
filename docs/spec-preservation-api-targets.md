# Preservation API: removal and caller inventory

Date: 2026-10-27. Status: IMPLEMENTING; source migration complete, Nix acceptance pending.
Audience: designers and reviewers.
Contract: [ADR 0025 D1/D4](adr-0025-compositional-preservation-proofs.md).
Companion: [proof and proposition changes](spec-preservation-proof-targets.md).

Names were checked against production revision `3e2212ed6983` on 2026-10-28. Unless qualified
otherwise, declarations are in `Belay.Sqlite.Model`. Linked files are current
owners. The six deleted wrapper owners remain as plain names in the baseline tables. The tables are a bounded work
inventory; they do not authorize deleting other declarations with similar names.

## Remove the 54 run specializations

Each row enumerates a Cartesian product: append each listed suffix to each
listed prefix. For example, `runSqlFrom_` with `notNull` means
`runSqlFrom_notNull`. These tables are the current removal inventory. The
[historical 84-name inventory](../experiments/proof-simplification/inventory.json)
records the original names, spans and consumers. Latest main replaced its 18
surface endpoints with all-execution claims; their current names appear below.
The 36 raw-run and 30 statement names are unchanged. Historical sizes are not
measurements of this revision.

| Baseline owner | Prefixes | Suffixes | Count |
| --- | --- | --- | --- |
| [ValidAtomsRuns][valid-runs] | `runSqlFrom_`, `runSql_` | `notNull`, `typesFit`, `checksHold` | 6 |
| [ValidAtomsTogether][together] | `runSqlFrom_`, `runSql_` | `constraintAtoms` | 2 |
| [KeysUniqueRuns][key-runs] | `runSqlFrom_`, `runSql_` | `keysUnique` | 2 |
| `AdmittedSqlRunsCatalog` (removed) | `runSqlFrom_`, `runSql_` | `catalogSupported`, `rowsShaped`, `rowidsDistinct`, `rowidsInRange` | 8 |
| `AdmittedSqlRunsRows` (removed) | `runSqlFrom_`, `runSql_` | `rowsWide`, `rowsStored`, `rowsAliased`, `admitted` | 8 |
| `ScriptRunAdmittedCatalog` (removed) | `runScriptAllFrom_` | `catalogSupported`, `rowsShaped`, `rowidsDistinct`, `rowidsInRange` | 4 |
| `ScriptRunAdmittedRows` (removed) | `runScriptAllFrom_` | `rowsWide`, `rowsStored`, `rowsAliased`, `admitted` | 4 |
| ScriptRunConstraints ([Schema/Rows][script-constraints-schema-rows], [Programs/Scripts][script-constraints-programs-scripts]) | `runScriptAllFrom_` | `keysUnique`, `notNull`, `typesFit`, `checksHold`, `constraintAtoms` | 5 |
| ForeignKeyRuns ([Schema/ForeignKeys][fk-runs-schema-foreignkeys], [Tooling/Counterexamples][fk-runs-tooling-counterexamples]) | `runSqlFrom_`, `runSql_`, `runScriptAllFrom_` | `rowReferences`, `foreignKeyAtoms` | 6 |
| [ForeignKeySchemaRuns][fk-schema] | `runSqlFrom_`, `runSql_`, `runScriptAllFrom_` | `parentSchemasCompatible` | 3 |
| ForeignKeySelectedRuns ([Programs/StatementRunLaws][fk-selected-programs-statementrunlaws], [Tooling/Counterexamples][fk-selected-tooling-counterexamples]) | `runSqlFrom_`, `runSql_`, `runScriptAllFrom_` | `parentSchemasCompatibleSelected`, `foreignKeyAtomsSelected` | 6 |

Replace these with generic raw/surface run laws applied to retained invariant
evidence. Preserve each current formula and its assumptions, including every
complete surface execution, selected versus explicit FK mappings, support,
execution mode and matching limits. Canonical-run claims follow by membership
in the complete executions. Remove names after callers migrate; no
compatibility aliases remain.

## Remove the 30 per-operation atom specializations

For each row, the full names are `runStatement_<operation>_<atom>`, for every
listed operation and each of `notNull`, `typesFit`, `checksHold`.

| Baseline owner | Operations | Count |
| --- | --- | --- |
| `RowLocalWriteTheorems` (removed) | `insert`, `update`, `delete`, `writesNone`, `upsert` | 15 |
| `RowLocalSchemaTheorems` (removed) | `createTable`, `createIndex`, `createTrigger`, `drop` | 12 |
| [RowLocalAddColumnTheorems][add-column] | `addColumn` | 3 |

Use the generic operation or whole-statement law with `Table.notNullAtom`,
`Table.typesFitAtom` or `Table.checksHoldAtom` and the original local hypotheses.
This list contains no per-atom CREATE VIEW wrapper.

The API migration deletes six pure-wrapper files: `AdmittedSqlRunsCatalog`, `AdmittedSqlRunsRows`,
`ScriptRunAdmittedCatalog`, `ScriptRunAdmittedRows`, `RowLocalWriteTheorems`,
`RowLocalSchemaTheorems`. Update [model imports](../packages/belay-sqlite-model/Belay/Sqlite/Model.lean)
and [Lake roots](../packages/belay-sqlite-model/lakefile.toml), plus direct imports
at callers. Other listed files contain retained declarations. Their replacements are
[generic raw run laws and readiness conditions](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/RunHolds.lean),
[derived surface laws](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/ScriptRunDerived.lean),
row-local writes ([Schema/Rows](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/RowLocalWrites.lean), [Programs/Scripts](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/RowLocalWrites.lean)) and
row-local schema facts ([Schema/Rows](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/RowLocalSchema.lean), [Programs/Scripts](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/RowLocalSchema.lean)).

## Remove duplicated predicates and condition aliases

These targets are additional to the 84 endpoints. Replace their uses with the
generic expression shown. This removes naming layers, not invariant premises.

| Baseline owner | Remove or replace | Generic expression or law |
| --- | --- | --- |
| [KeysUniqueFrame][key-frame] | `Effect.KeysUnique`; `Effect.keysUnique_of_effectDatabase`; `Effect.keysUnique_of_database` | `Effect.Satisfies Database.KeysUnique`; `Effect.satisfies_of_effectDatabase`; `Effect.satisfies_of_database` |
| [KeysUniqueRunStep][key-step] | `SqlState.KeysUnique`; `Outcome.KeysUnique` | `SqlState.Holds Database.KeysUnique`; `Outcome.Holds Database.KeysUnique` |
| [KeysUniqueRuns][key-runs] | `RunConditions`; `RunConditions.of_unconditioned` | `RunConditionsWith` with `Resolved.Statement.RunCondition`; its generic `of_unconditioned` law |
| [ValidAtomsRuns][valid-runs] | `NotNullRunConditions`; `TypesFitRunConditions`; `ChecksHoldRunConditions` | `RunConditionsWith` with the corresponding statement condition |
| [ValidAtomsTogether][together] | `AtomsRunConditions` | `RunConditionsWith` with `Resolved.Statement.AtomsCondition` |

The generic condition interface then changes as specified in the companion
inventory. Do not preserve an old-condition adapter in the production API.

## Keep distinct propositions and semantic results

The following are retained boundaries, even where their file also loses wrappers.

| Current owner | Declarations and intended treatment |
| --- | --- |
| [DatabaseConstraints](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/DatabaseConstraints.lean) | Preserve `Database.NotNull`, `Database.TypesFit`, `Database.ChecksHold`, `Database.KeysUnique` and their table-level definitions. |
| ValidAtomsStatement ([Schema/Columns](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Columns/ValidAtomsStatement.lean), [Programs/StatementRunLaws](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/ValidAtomsStatement.lean)) | Preserve `Resolved.Statement.NotNullCondition`, `.TypesFitCondition`, `.ChecksHoldCondition`; preserve `runStatement_notNull`, `runStatement_typesFit`, `runStatement_checksHold` as independent evidence. |
| [KeysUniqueRunStep][key-step], KeysUniqueStatement ([Schema/Columns](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Columns/KeysUniqueStatement.lean), [Programs/StatementRunLaws](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/KeysUniqueStatement.lean)) | Preserve the meanings of `Resolved.Statement.RunCondition`, `.KeysCondition`, `.unconditioned`, `.keysCondition_of_runCondition`, `.runCondition_of_unconditioned` and `runStatement_keysUnique`. |
| [ValidAtomsTogether][together] | Preserve `Database.ConstraintAtoms`, `Database.Valid.constraintAtoms`, `Resolved.Statement.AtomsCondition`, `.atomsCondition_of_unconditioned`; move/generalize conjunction evidence where needed. |
| [RowLocalAddColumnTheorems][add-column] | Preserve `Table.NotNull.appendColumn`, `Table.TypesFit.appendColumn`, `Table.ChecksHold.appendColumn`, `Table.allChecks_appendColumn` and `runStatement_addColumn_rowLocal`. |
| [RowLocalAddColumn](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Columns/RowLocalAddColumn.lean) | Preserve `Database.RowsWideAt`, `Database.StrictDefaultFitsAt`, `Database.ChecksReadBelowAt`; these encode distinct necessary premises. |
| ScriptRunConstraints ([Schema/Rows][script-constraints-schema-rows], [Programs/Scripts][script-constraints-programs-scripts]) | Retain `Database.AdmittedWith` and generic `runScriptAllFrom_admittedWith`; migrate their proof interface. |
| ScriptRunValid ([Schema/Rows][valid-schema-rows], [Programs/StatementRunLaws][valid-programs-statementrunlaws]) | Retain `Database.valid_iff`, `Database.valid_empty`, `runScriptAllFrom_valid`, `runScriptStep_valid`; preserve the latter's guarantee for every `RunStep.executions` member. |
| ForeignKeyRuns ([Schema/ForeignKeys][fk-runs-schema-foreignkeys], [Tooling/Counterexamples][fk-runs-tooling-counterexamples]) | Retain `Database.ParentSchemasCompatible.rowReferences_iff_selected` and `runStatement_foreignKeyAtoms`; migrate the preservation certificates listed in the companion. |
| [ForeignKeyStatement](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/ForeignKeys/ForeignKeyStatement.lean), [ForeignKeySelectedStatement](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/ForeignKeys/ForeignKeySelectedStatement.lean) | Preserve `Resolved.Statement.ForeignKeyRowsCondition`, `.ForeignKeySchemaCondition`, `.ForeignKeyAtomsCondition`: rename requires equal `selectedParents`; DROP COLUMN requires no additional condition. |
| [KeysUniqueLookup](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/KeysUniqueLookup.lean) | Retain `Table.KeysUnique.lookup` and `Database.KeysUnique.lookup`; uniqueness lookup is not a run wrapper. |

## Migrate clients and retire duplicate formula checks

| Existing file or registration | Intended change |
| --- | --- |
| ScriptRunValid ([Schema/Rows][valid-schema-rows], [Programs/StatementRunLaws][valid-programs-statementrunlaws]) | Rewrite `runScriptAllFrom_valid` and `runScriptStep_valid` through retained generic evidence. |
| [KeysUniqueRunExamples](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/KeysUniqueRunExamples.lean) | Migrate `cascadeScript_keysUnique` and anonymous condition examples to generic predicates/run laws. |
| [ValidAtomsExamples](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/ValidAtomsExamples.lean) | Migrate `strictCascadeScript_constraintAtoms`, `setNullScript_notNull` and their condition proofs. |
| [AdmittedRunsExamples](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/AdmittedRunsExamples.lean), AdmittedRunsConditionExamples ([Queries/Preparation](../packages/belay-sqlite-model/Belay/Sqlite/Model/Queries/Preparation/AdmittedRunsConditionExamples.lean), [Schema/Ddl](../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Ddl/AdmittedRunsConditionExamples.lean), [Programs/Scripts](../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/AdmittedRunsConditionExamples.lean)) | Migrate `mixedRun_rowsAliased` and anonymous run formulas; retain necessity counterexamples and `mixedRun_valid`. |
| [ProgramRun](../packages/belay/Belay/Sqlite/Programs/Scripts/ProgramRun.lean), [ProgramLaws](../packages/belay/Belay/Sqlite/Programs/Scripts/ProgramLaws.lean) | Recompile callers of the retained Valid helpers; change only if their proof application or imports require it. |
| [valid_atoms_theorems_test.py](../tests/valid_atoms_theorems_test.py) | Retire 12 run endpoint checks after migration acceptance; preserve independent whole-statement contracts/premise coverage. |
| [keys_unique_theorems_test.py](../tests/keys_unique_theorems_test.py) | Retire three run endpoint checks; migrate the statement and lookup checks to generic effect/state predicates. |
| [admitted_atoms_run_theorems_test.py](../tests/admitted_atoms_run_theorems_test.py) | Retire the `ATOMS` × three prefixes matrix and removed constraint-wrapper audit entries; retain/rehome four Valid helper/definition checks. |
| [ForeignKeyRuns](../tests/surface/Schema/Tests/ForeignKeyRuns.lean), [ForeignKeySchemaRuns](../tests/surface/Schema/ForeignKeys/ForeignKeySchemaRuns.lean), [ForeignKeyDdlRuns](../tests/surface/Schema/Tests/ForeignKeyDdlRuns.lean), [ForeignKeyDdlDropRuns](../tests/surface/Schema/ForeignKeys/ForeignKeyDdlDropRuns.lean) | Migrate fixed/selected mapping and reached-run examples; retain their semantic cases where coverage is unique. |
| [ForeignKeyStatementAxioms](../tests/surface/Schema/ForeignKeys/ForeignKeyStatementAxioms.lean), [nix_suites.json](../tests/nix_suites.json) | Replace retired endpoint audit roots with generic proofs and independent evidence; remove obsolete registrations after final acceptance. |

DROP COLUMN adds a statement case, not new per-atom endpoints to this removal
set. Its execution guard supplies its preservation premises. For rename, the
current executor checks `Catalog.sameOutline`, which does not imply equal
selected parents. Preserve the explicit FK premise instead of restoring the
older unconditional rename claim. Catalog-preserving `KeepsParentSchema`
continues to exclude both operations.

These are named starting clients, not a claim that literal search finds every
reference. Check generated test names, checked doc references, exports and
imports during implementation. Keep one temporary complete formula witness
set against `3e2212ed6983`, including its stronger surface contracts, through the
last affected contract change. Historical experiments do not establish those
new claims. Then record Nix acceptance and remove redundant active witnesses
and registrations under ADR 0025 D4. Do not add
a permanent test or CI inventory that freezes this table.

[valid-runs]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/ValidAtomsRuns.lean
[together]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/ValidAtomsTogether.lean
[key-runs]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/KeysUniqueRuns.lean
[script-constraints-schema-rows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/ScriptRunConstraints.lean
[script-constraints-programs-scripts]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/ScriptRunConstraints.lean
[fk-runs-schema-foreignkeys]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/ForeignKeys/ForeignKeyRuns.lean
[fk-runs-tooling-counterexamples]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Tooling/Counterexamples/ForeignKeyRuns.lean
[fk-schema]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/ForeignKeySchemaRuns.lean
[fk-selected-programs-statementrunlaws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/ForeignKeySelectedRuns.lean
[fk-selected-tooling-counterexamples]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Tooling/Counterexamples/ForeignKeySelectedRuns.lean
[add-column]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Columns/RowLocalAddColumnTheorems.lean
[key-frame]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/KeysUniqueFrame.lean
[key-step]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Columns/KeysUniqueRunStep.lean
[valid-schema-rows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Rows/ScriptRunValid.lean
[valid-programs-statementrunlaws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/ScriptRunValid.lean
