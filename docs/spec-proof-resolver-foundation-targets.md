# Resolver and foundation change targets

Date: 2026-10-27. Status: PROPOSED; implementation has not started.
Audience: designers and reviewers.
Contract: [resolver and foundation specification](spec-proof-foundations.md).
Decisions: [ADR 0026 D3, D6 and D7](adr-0026-semantic-proof-boundaries.md).
Evidence: [resolver/import findings](../experiments/proof-boundaries/resolver-import-findings.md)
and [deferred row-engine findings](../experiments/proof-boundaries/row-engine-findings.md).

This inventory was checked against production revision `3fe5caef`.
Model declaration names below have prefix `Belay.Sqlite.Model`. Surface names
have prefix `Belay.Sqlite`. Fixed replacements and relocations are distinguished
from placement choices, reused facts and consumers that need only recompilation.
Check branch drift at assignment; this list is not a permanent inventory gate.

## Replace three resolver dispatches

| Fixed declaration to replace | Current file | Guarantee retained by the certificate |
| --- | --- | --- |
| `resolveStatement_after` | [Resolution/ResolveStateSpec.lean][state-spec] | Successful resolution determines the entire next state, without validity or mode premises. |
| `resolveStatement_schemaLink` | [ResolveStatementFacts.lean][statement-facts] | Input-catalog validity at any supplied limits gives `SchemaLink`; no saved-catalog or execution-mode premise. |
| `resolveStatement_valid` | [ResolveStatementValid.lean][statement-valid] | Execution mode and validity of the current and saved catalogs at the context profile's limits give full next-state validity. |

One syntax dispatch replaces these proofs; delete their names after caller
migration. The exact old formulas remain temporary acceptance obligations.
The experimental `ResolverCertificate`, `CatalogCertificate`,
`certificate_withCatalog`, `certificate_withWrite` and `resolve_certificate`
in [the certificate](../experiments/proof-boundaries/ResolverCertificate.lean)
and [dispatch](../experiments/proof-boundaries/ResolverDispatch.lean) demonstrate
the boundary. Their names, record layout and destination files are choices.
BEGIN, COMMIT, ROLLBACK, settings, prepare errors and write rules retain their
actual state behavior; the certificate fields keep separate premises.

## Separate prerequisites from their consumers

These are exact ownership targets, not additional formula replacements.
Move a prerequisite or split its present owner as needed to put it below the
shared dispatch. Keeping a suitable existing owner after deleting its old
dispatch is also valid; no new global foundation package is required.

| Declaration | Current owner | Required boundary |
| --- | --- | --- |
| `ResolveState.Valid` | [ResolveStatementValid.lean][statement-valid] | Current and optional saved catalog validity must be available without importing the script validity proof. |
| `ResolveState.after`, `ResolveState.after_of_isControl` | [Resolution/ResolveStateSpec.lean][state-spec] | Exact transaction/settings/catalog transition and its ordinary-statement reduction sit below certificate consumers. |
| `Resolved.Statement.SchemaLink` | [ResolveStatementForms.lean][forms] | ADD COLUMN strict-default fit, DROP closure, and the vacuous other cases remain usable independently of the new dispatch. |

In particular, `ResolveStatementValid.lean` also owns `resolve_valid`. A new
certificate that imports that file cannot be imported back by its script proof.
Reorganize that dependency without copying `ResolveState.Valid`.
`ResolveState.withWrite_cases` in [Resolution/ResolveState.lean][resolve-state],
and `Resolved.Statement.schemaLink_withRules` and
`ResolveState.withWrite_schemaLink` in [ResolveStatementLink.lean][statement-link],
are reusable transport facts. They are not replaced dispatches.

## Migrate resolver consumers and preserve downstream claims

| Current file | Exact declaration or source use | Required change or check |
| --- | --- | --- |
| [ResolveStatementApplied.lean][applied] | `resolveStatement_applyCatalog_valid` | Use the certificate; keep the formula for controls too, using `Resolved.Statement.applyCatalog_of_control`. |
| [ResolveStatementValid.lean][statement-valid] | `resolve_valid` | Use the conditional validity field in the script induction; preserve execution mode, profile limits and saved-state reasoning. |
| [Resolution/ResolveFoldSpec.lean][fold] | `resolveFrom_after` | Use the unconditional state field in the fold proof. Recompile the derived `resolve_after` claim. |
| [ScriptRunLaws.lean][script-laws] | `Connection.resolveState_after_next` | Replace the state-equation call; retain arbitrary resolution context. Update the old-name references in `runScriptFrom_agrees` documentation and recompile it. |
| [ScriptRunConstraints.lean][script-constraints] | `runScriptFrom_admittedWith` | Replace the schema-link call with its field at the existing limits. Coordinate this consumer with ADR 0025's script refactor. |
| [SuccessfulScriptEffects.lean][effects] | `runScriptStep_effect` | Replace the state-equation call while keeping the non-control and actual successful-output premises. |
| [AdmittedRunsConditionExamples.lean][condition-examples] | Anonymous DROP TABLE schema-link example | Migrate the direct `resolveStatement_schemaLink` use; retain its focused catalog-link coverage. |
| [ScriptRunApplied.lean][script-applied] | `Connection.resolveState_valid`, `resolveStatement_appliedValid` | Recompile/migrate imports after prerequisite moves; preserve the database/snapshot bridge and equality of profile limits. These are not nominated deletions. |

This table distinguishes direct body migrations from immediate downstream
checks. Update source imports and checked documentation, then compile the full
affected consumers; it does not claim to enumerate every transitive user.

## Reuse leaf resolver facts

These are the existing evidence families used by the experiment, not a mandate
to edit every listed declaration. Keep their independent, sometimes weaker,
premises. Relocate a leaf only if the chosen module boundary requires it.

| Existing owner | Reused declarations |
| --- | --- |
| [Resolution/ResolveStateSpec.lean][state-spec] | `resolveCreateTable_applyCatalog`, `resolveCreateIndex_applyCatalog`, `resolveAddColumn_applyCatalog` |
| [Resolution/DropSpec.lean][drop-spec] | `resolveDropTable_applyCatalog`, `resolveDropIndex_applyCatalog`, `resolveDropView_applyCatalog` |
| [Resolution/TriggerDefinitionSpec.lean][trigger-spec]; [Resolution/ViewDefinitionSpec.lean][view-spec] | `resolveCreateTrigger_applyCatalog`, `resolveDropTrigger_applyCatalog`; `resolveCreateView_applyCatalog` |
| [Resolution/WriteCatalogSpec.lean][write-spec]; [Resolution/SelectResolution.lean][select-resolution] | `resolveInsert_same`, `resolveUpdate_same`, `resolveDelete_same`, `resolveCommonTableWrite_same`; `resolveSelect_same` |
| [ResolveStatementForms.lean][forms] | `resolveCreateTable_schemaLink`, `resolveCreateIndex_schemaLink`, `resolveCreateTrigger_schemaLink`, `resolveInsert_schemaLink`, `resolveUpdate_schemaLink`, `resolveDelete_schemaLink`, `resolveSelect_schemaLink`, `resolveCommonTableWrite_schemaLink` |
| [ResolveStatementLink.lean][statement-link] | `resolveCreateView_schemaLink`, `resolveAddColumn_schemaLink`, `resolveDropTable_schemaLink`, `resolveDropIndex_schemaLink`, `resolveDropTrigger_schemaLink`, `resolveDropView_schemaLink` |
| [ResolveCreateTableCatalog.lean][create-table]; [ResolveCreateIndexCatalog.lean][create-index]; [ResolveCreateTriggerCatalog.lean][create-trigger]; [ResolveCreateViewCatalog.lean][create-view]; [ResolveAddColumnCatalog.lean][add-column] | Respectively `resolveCreateTable_valid`, `resolveCreateIndex_valid`, `resolveCreateTrigger_valid`, `resolveCreateView_valid`, `resolveAddColumn_valid` |
| [ResolveDropValid.lean][drop-valid] | `resolveDropTable_valid`, `resolveDropIndex_valid`, `resolveDropTrigger_valid`, `resolveDropView_valid` |
| [Resolution/ViewTableInfo.lean][pragma-cases]; [ResolveStatementPragmaLink.lean][pragma-link] | `resolveStatementPragma_cases`; `resolveStatementPragma_schemaLink` |

## Relocate four primitives without changing their formulas

The declarations are fixed targets. The lower owners suggested here are
placement choices, subject to compilation, file-size limits and cycle checks.
The [primitive experiment](../experiments/proof-boundaries/ImportsPrimitives.lean)
uses combined lower imports; it does not prove each proposed owner is minimal.

| Existing declaration and owner | Proposed lower domain/root | Retained condition and consumer scope |
| --- | --- | --- |
| `Collation.compare_eq_of_binary` in [ForeignKeySelfLookup.lean][self-lookup] | `Comparison` laws | BINARY comparison equals `.eq`; every built-in collation then compares equal. Migrate `LiteralData.keyCellsEqual_of_binary` and `equalsParameter_true` in `PlainInsertRows.lean`. |
| `NormalizedField.generatedCells_plain` in [NormalizedFieldRows.lean][normalized-rows] | Generated-cell laws alongside `AdmittedCellLaws` | Every column has `generated = none`; any input cell list is unchanged. Migrate `NormalizedField.assign_lower_append`, `LiteralData.inserted_plain` and `LiteralData.newCells_getElem?_of_plain` in `PlainInsertRows`. |
| `Database.tableAt_of_table` in [AddColumnFromValid.lean][add-valid] | Database lookup laws alongside `DatabaseFacts` | A successful database table lookup gives the corresponding catalog shape; no catalog-validity premise. Recompile the owner, `AdmittedPlainWrites`, `ForeignKeyAddColumnReads`, `ForeignKeyAddColumn`, `ForeignKeyDdlSelected` and `ForeignKeySelectedStatement`. |
| `Database.table_of_findTable` in [TableSourceLaws.lean][table-source] | Database/catalog lookup laws with `DatabaseFacts` and `Resolution.CatalogSpec` | Successful named catalog lookup gives the database table and its stored rows; no admission premise. Recompile `CreateIndexSuccessLaws` and surface query consumers. |

The last row's surface consumers are `AggregateQuery`, `ColumnQuery`,
`CountQuery`, `DuplicateKeyQuery`, `ExistsQuery`, `NotExistsQuery`,
`SelectOneFrom`, `SelectOneMayFail` and `UniqueLookupQuery`, under
[packages/belay/Belay/Sqlite](../packages/belay/Belay/Sqlite).
Coordinate their proof migrations with the query specification. Relocation
alone need not change a theorem's qualified name; do not leave duplicate aliases.
Preserve public aggregation in [Belay.Sqlite.Model](../packages/belay-sqlite-model/Belay/Sqlite/Model.lean).

## Narrow three surface imports

These module edits are fixed. The listed model roots are the compiled proposed
sets from [imports.py](../experiments/proof-boundaries/imports.py), not optimality
claims. Keep the rest of each module's body and other imports.

| Surface module | Replace the `Belay.Sqlite.Model` umbrella with model roots | Preserve |
| --- | --- | --- |
| [Values.lean][values] | `Comparison`, `Declarations`, `StoreValue`, `StoreValueLaws`, `Truth` | All exported model names, literal/coercion instances and checked documentation. |
| [Script.lean][script] | `Declarations`, `Resolution.Syntax`, `SqlAdvance` | `Script`, `Script.empty`, append instance/laws, `Script.withValues`, `Script.withValues_statements`. |
| [ValueDisplay.lean][display] | `Declarations`, `OutputRepr` | `ToString Value`, `unexpandIntegerValue` and its `app_unexpander` registration; retain the Lean delaborator import. |

Rebuild downstream clients that may have relied on transitive umbrella names.
Project import closures measured 580→75, 580→142 and 580→148 respectively;
these are source-import measurements, not timing or permanent CI thresholds.

## Explicitly deferred row-engine targets

The following inventory explains what this decision leaves specialized. It is
not an implementation backlog and does not freeze unrelated ADR 0025 work.

| Current owner | Deferred shared-interface replacement targets |
| --- | --- |
| [RowEngineTriggers.lean][row-triggers] | `NestedRun.Keeps`, `ProgramResult.Holds`; `raiseEffect_holds`, `runStep_holds`, `enterProgram_holds`, `runProgram_holds`, `runPrograms_holds` |
| [ForeignKeyCounterTriggers.lean][fk-triggers] | `raiseEffect_foreignKeyInvariant`, `runStep_counterBound`, `enterProgram_counterBound`, `runProgram_counterBound`, `runPrograms_counterBound` |
| [ForeignKeyWorkConditions.lean][work-conditions] | `ForeignKeyUpdateConditions`, `RowWork.ForeignKeySafe`, `Resolved.Step.ForeignKeySafe`, `ProgramsForeignKeySafe`, `ActionsForeignKeySafe`, `NestedRun.ForeignKeyKeeps`, `NestedRun.BeforeUpdateFrame` |
| [ForeignKeyEngineFacts.lean][engine-facts] | `Database.ForeignKeyReady`, `KeyState.ForeignKeyInvariant`, `KeyStop.ForeignKeyInvariant` retain their separate state/stop contracts. |
| [RowEngineWrites.lean][row-writes]; [ForeignKeyCounterRows.lean][fk-rows] | `runRows_holds`; `runRows_foreignKeyKeeps` fuel inductions were not generalized by either prototype. |
| [ForeignKeyCounterDelete.lean][fk-delete] | `deleteRow_counterBound` retains its combined check/removal phase; no per-micro-operation invariant is introduced. |

The ten trigger proof bodies and their compact row-operation consumers stay.
FAIL retains the full FK bound; rollback requires the database facts only;
raw errors and undescribed stops impose no state condition. Generated-work
permission and BEFORE UPDATE frame conditions remain independent obligations.
Do not add `RowKeeps`, `StepAllowed` or the narrow experimental wrappers to
production. The [five Row experiments](../experiments/proof-boundaries/row-engine-findings.md)
remain historical evidence, with no requirement to port their tests.

## Acceptance and test lifetime

Use the linked specification's formula, trust, consumer-build and ownership
checks. This inventory creates no checker, manifest, task file or CI snapshot.
Old/new formula witnesses, copied primitive proofs and baseline/narrow modules
are temporary acceptance work. Keep unique premise/transaction/trust coverage
until migrated clients or focused regressions supply it; after final Nix
acceptance, retire redundant active witnesses and registrations as ADR 0026
requires. Record acceptance and retirement in the existing status file.

[state-spec]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ResolveStateSpec.lean
[statement-facts]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveStatementFacts.lean
[statement-valid]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveStatementValid.lean
[forms]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveStatementForms.lean
[resolve-state]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ResolveState.lean
[statement-link]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveStatementLink.lean
[applied]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveStatementApplied.lean
[fold]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ResolveFoldSpec.lean
[script-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunLaws.lean
[script-constraints]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunConstraints.lean
[effects]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/SuccessfulScriptEffects.lean
[condition-examples]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedRunsConditionExamples.lean
[script-applied]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ScriptRunApplied.lean
[drop-spec]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/DropSpec.lean
[trigger-spec]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/TriggerDefinitionSpec.lean
[view-spec]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ViewDefinitionSpec.lean
[write-spec]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/WriteCatalogSpec.lean
[select-resolution]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/SelectResolution.lean
[create-table]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveCreateTableCatalog.lean
[create-index]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveCreateIndexCatalog.lean
[create-trigger]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveCreateTriggerCatalog.lean
[create-view]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveCreateViewCatalog.lean
[add-column]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveAddColumnCatalog.lean
[drop-valid]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveDropValid.lean
[pragma-cases]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ViewTableInfo.lean
[pragma-link]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ResolveStatementPragmaLink.lean
[self-lookup]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeySelfLookup.lean
[normalized-rows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/NormalizedFieldRows.lean
[add-valid]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AddColumnFromValid.lean
[table-source]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TableSourceLaws.lean
[values]: ../packages/belay/Belay/Sqlite/Values.lean
[script]: ../packages/belay/Belay/Sqlite/Script.lean
[display]: ../packages/belay/Belay/Sqlite/ValueDisplay.lean
[row-triggers]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowEngineTriggers.lean
[fk-triggers]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeyCounterTriggers.lean
[work-conditions]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeyWorkConditions.lean
[engine-facts]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeyEngineFacts.lean
[row-writes]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowEngineWrites.lean
[fk-rows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeyCounterRows.lean
[fk-delete]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ForeignKeyCounterDelete.lean
