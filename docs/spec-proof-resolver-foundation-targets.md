# Resolver and foundation change targets

Date: 2026-10-27. Revised: 2026-10-28. Status: PROPOSED; one primitive move is delivered.
Audience: designers and reviewers.
Contract: [resolver and foundation specification](spec-proof-foundations.md).
Decisions: [ADR 0026 D3, D6 and D7](adr-0026-semantic-proof-boundaries.md).
Evidence: [resolver/import findings](../experiments/proof-boundaries/resolver-import-findings.md), [deferred row-engine findings](../experiments/proof-boundaries/row-engine-findings.md).

Source review: `3e2212ed`; compiled experiments/measurements: historical `3fe5caef`.
Model names have prefix `Belay.Sqlite.Model`; surface names, `Belay.Sqlite`.
Fixed changes are distinguished from placement choices, reused facts and compile checks.
Check branch drift at assignment; this is not a permanent inventory gate.

## Replace three resolver dispatches

| Fixed declaration to replace | Current file | Guarantee retained by the certificate |
| --- | --- | --- |
| `resolveStatement_after` | [Resolution/ResolveStateSpec.lean][state-spec] | Successful resolution determines the entire next state, without validity or mode premises. |
| `resolveStatement_schemaLink` | [ResolveStatementFacts.lean][statement-facts] | Input-catalog validity at any supplied limits gives `SchemaLink`; no saved-catalog or execution-mode premise. |
| `resolveStatement_valid` | [ResolveStatementValid.lean][statement-valid] | Execution mode and validity of the current and saved catalogs at the context profile's limits give full next-state validity. |

One syntax dispatch replaces these proofs; delete their names after caller
migration. The exact old formulas remain temporary acceptance obligations.
The historical [certificate](../experiments/proof-boundaries/ResolverCertificate.lean)
and [dispatch](../experiments/proof-boundaries/ResolverDispatch.lean) demonstrate
`ResolverCertificate`, `CatalogCertificate`, `certificate_withCatalog`,
`certificate_withWrite` and `resolve_certificate`; their names/layout are choices.
Required coverage includes `Syntax.Statement.renameTable`, `renameColumn`, `dropColumn`
and `insertSelect`; retain resolved `rewrite`/`dropColumn`/`insertSelect`, transactions, settings,
prepare errors and write rules. The old prototype has not validated these additions.
Reuse the projection `resolveStatementRun` → `resolveStatementTraced` →
`resolveStatement` in [Resolution/ResolveStatement.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ResolveStatement.lean)
and `resolveStatementTraced_fst`/`statement_arms` in [Resolution/StatementArms.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/StatementArms.lean); preserve name traces and registrations.
Preserve PR #292: executable [Resolution/Resolve.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Resolve.lean) imports `ResolveStatement`, not `StatementArms`.
Proof clients import equations explicitly; certificate placement must keep them out of executable/mutant dependencies.

## Separate prerequisites from their consumers

These are ownership targets, not formula replacements. Move a prerequisite or
split its owner to put it below the dispatch; an existing suitable owner can stay.

| Declaration | Current owner | Required boundary |
| --- | --- | --- |
| `ResolveState.Valid` | [ResolveStatementValid.lean][statement-valid] | Current and optional saved catalog validity must be available without importing the script validity proof. |
| `ResolveState.after`, `ResolveState.after_of_isControl` | [Resolution/ResolveStateSpec.lean][state-spec] | Exact transaction/settings/catalog transition and its ordinary-statement reduction sit below certificate consumers. |
| `Resolved.Statement.SchemaLink` | [ResolveStatementForms.lean][forms] | ADD COLUMN strict-default fit, DROP closure, and vacuous other cases (including `rewrite`/`dropColumn`/`insertSelect`) stay independently usable. |

`ResolveStatementValid.lean` also owns `resolve_valid`: split that dependency
without copying `ResolveState.Valid` before its script proof imports the certificate.
Reuse `ResolveState.withWrite_cases` in [Resolution/ResolveState.lean][resolve-state],
and `Resolved.Statement.schemaLink_withRules`/`ResolveState.withWrite_schemaLink` in [ResolveStatementLink.lean][statement-link].

## Migrate resolver consumers and preserve downstream claims

| Current file | Exact declaration or source use | Required change or check |
| --- | --- | --- |
| [ResolveStatementApplied.lean][applied] | `resolveStatement_applyCatalog_valid` | Use the certificate; keep the formula for controls too, using `Resolved.Statement.applyCatalog_of_control`. |
| [ResolveStatementValid.lean][statement-valid] | `resolve_valid` | Use the conditional validity field in the script induction; preserve execution mode, profile limits and saved-state reasoning. |
| [Resolution/ResolveFoldSpec.lean][fold] | `resolveFrom_after` | Use the unconditional state field in the fold proof. Recompile the derived `resolve_after` claim. |
| [ScriptRunLaws.lean][script-laws] | `Connection.resolveState_after_next` | Replace the state-equation call; retain arbitrary resolution context. Update the old-name references in `runScriptFrom_agrees` documentation and recompile it. |
| [ScriptRunConstraints.lean][script-constraints] | `runScriptAllFrom_admittedWith` | Replace the schema-link call; retain the guarantee for every complete execution, not just `runScriptFrom`. Coordinate with ADR 0025. |
| [SuccessfulScriptEffects.lean][effects] | `runScriptStep_effect` | Keep non-control/success premises and `.continued output next others`, with separate actual result and `others : List StatementExecution`. |
| [FailedStepFrame.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/FailedStepFrame.lean) | `runScriptStep_failed_frame` | Replace its state-equation call; retain the explicit failed-effect/frame premises. |
| [PlainWriteFrame.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/PlainWriteFrame.lean); [ReadOnlyFrame.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/ReadOnlyFrame.lean) | `runScriptStep_plainWrite_frame`; `runScriptStep_readOnly_keeps` | Replace state-equation calls; retain each form premise that establishes `others = []` and its connection frame. |
| [ControlStepLaws.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/ControlStepLaws.lean) | `runScriptStep_begin_idle`, `runScriptStep_begin_active`, `runScriptStep_commit_active`, `runScriptStep_commit_idle` | Replace state-equation calls; preserve distinct snapshot and transaction cases. |
| [PragmaStepLaws.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/PragmaStepLaws.lean); [ExecutionEffects.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/ExecutionEffects.lean) | `runScriptStep_setting`; `runScriptStep_execution_effects` | Replace state-equation calls. The latter covers every successful execution with a listed effect, not a unique corresponding run. |
| [AdmittedRunsConditionExamples.lean][condition-examples] | Anonymous DROP TABLE schema-link example | Migrate the direct `resolveStatement_schemaLink` use; retain its focused catalog-link coverage. |
| [ScriptRunApplied.lean][script-applied] | `Connection.resolveState_valid`, `resolveStatement_appliedValid` | Recompile/migrate imports after prerequisite moves; preserve the database/snapshot bridge and equality of profile limits. These are not nominated deletions. |

Compile downstream `SchemaStepRules`, `ControlStepRules`, `SendStatementsInvariant`
and `SendStatementsSuccess`; their existing frame/success conditions remain.
`ReadCertificate` clients keep calmness, width, resolution and frame premises.
`moved` permits named tables at different positions; `preservesAt` uses obligations
for each migration branch. Keep `preservesAt_send`'s no-INSERT-SELECT premise and
the commutation theorem's own branch conditions; these are not resolver certificates.

## Reuse leaf resolver facts

These reused families are not all edit targets. Retain their independent premises.

| Existing owner | Reused declarations |
| --- | --- |
| [Resolution/ApplyCatalogSpec.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ApplyCatalogSpec.lean) | `resolveCreateTable_applyCatalog`, `resolveCreateIndex_applyCatalog`, `resolveAddColumn_applyCatalog` (moved from `ResolveStateSpec`) |
| [Resolution/RenameSpec.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/RenameSpec.lean) | `RenameOutcome`, `resolveRenameTable_outcome`, `resolveRenameColumn_outcome`, `RenameOutcome.applyCatalog`, `RenameOutcome.valid`; reuse these existing certificates. |
| [Resolution/DropColumnOutcome.lean](../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/DropColumnOutcome.lean) | `DropOutcome`, `resolveDropColumn_outcome`, `DropOutcome.applyCatalog`, `DropOutcome.valid`; retain the prepare-error branch and successful-drop droppable/output-supported evidence. |
| [Resolution/DropSpec.lean][drop-spec] | `resolveDropTable_applyCatalog`, `resolveDropIndex_applyCatalog`, `resolveDropView_applyCatalog` |
| [Resolution/TriggerDefinitionSpec.lean][trigger-spec]; [Resolution/ViewDefinitionSpec.lean][view-spec] | `resolveCreateTrigger_applyCatalog`, `resolveDropTrigger_applyCatalog`; `resolveCreateView_applyCatalog` |
| [Resolution/WriteCatalogSpec.lean][write-spec]; [Resolution/SelectResolution.lean][select-resolution] | `resolveInsert_same`, `resolveUpdate_same`, `resolveDelete_same`, `resolveCommonTableWrite_same`; new `resolveInsertQuery_form`/`resolveInsertQuery_same` use success of `resolveInsertQueryTraced(...).drop`; `resolveSelect_same` retains its existing role. |
| [ResolveStatementForms.lean][forms] | `resolveCreateTable_schemaLink`, `resolveCreateIndex_schemaLink`, `resolveCreateTrigger_schemaLink`, `resolveInsert_schemaLink`, `resolveUpdate_schemaLink`, `resolveDelete_schemaLink`, `resolveSelect_schemaLink`, `resolveCommonTableWrite_schemaLink` |
| [ResolveStatementLink.lean][statement-link] | `resolveCreateView_schemaLink`, `resolveAddColumn_schemaLink`, `resolveDropTable_schemaLink`, `resolveDropIndex_schemaLink`, `resolveDropTrigger_schemaLink`, `resolveDropView_schemaLink` |
| [ResolveCreateTableCatalog.lean][create-table]; [ResolveCreateIndexCatalog.lean][create-index]; [ResolveCreateTriggerCatalog.lean][create-trigger]; [ResolveCreateViewCatalog.lean][create-view]; [ResolveAddColumnCatalog.lean][add-column] | Respectively `resolveCreateTable_valid`, `resolveCreateIndex_valid`, `resolveCreateTrigger_valid`, `resolveCreateView_valid`, `resolveAddColumn_valid` |
| [ResolveDropValid.lean][drop-valid] | `resolveDropTable_valid`, `resolveDropIndex_valid`, `resolveDropTrigger_valid`, `resolveDropView_valid` |
| [Resolution/ViewTableInfo.lean][pragma-cases]; [ResolveStatementPragmaLink.lean][pragma-link] | `resolveStatementPragma_cases`; `resolveStatementPragma_schemaLink` |

## Relocate three primitives; reuse the delivered fourth

Lower owners remain choices subject to compilation, file-size and cycle checks.
The historical [primitive experiment](../experiments/proof-boundaries/ImportsPrimitives.lean) establishes no minimum import set.

| Existing declaration and owner | Proposed lower domain/root | Retained condition and consumer scope |
| --- | --- | --- |
| `Collation.compare_eq_of_binary` in [ForeignKeySelfLookup.lean][self-lookup] | `Comparison` laws | BINARY comparison equals `.eq`; every built-in collation then compares equal. Migrate `LiteralData.keyCellsEqual_of_binary` and `equalsParameter_true` in `PlainInsertRows.lean`. |
| `Database.tableAt_of_table` in [AddColumnFromValid.lean][add-valid] | Database lookup laws alongside `DatabaseFacts` | A successful database table lookup gives the corresponding catalog shape; no catalog-validity premise. Recompile the owner, `AdmittedPlainWrites`, `ForeignKeyAddColumnReads`, `ForeignKeyAddColumn`, `ForeignKeyDdlSelected` and `ForeignKeySelectedStatement`. |
| `Database.table_of_findTable` in [TableSourceLaws.lean][table-source] | Database/catalog lookup laws with `DatabaseFacts` and `Resolution.CatalogSpec` | Named catalog lookup gives the database table/rows without admission. Recompile `CreateIndexSuccessLaws`, `Database.rows_length_addDerivedColumn` in `DerivedColumnTable`, and `Database.tableNamed_some`/`Database.tableNamed_rewrite` in `TableByName`, plus surface consumers. |

Already delivered: `LiteralData.generatedCells_plain` in [AdmittedCellLaws.lean][cell-laws] retains the no-generated-columns identity.
Reuse it in `assign_derived_append` (`DerivedColumnRows`), `LiteralData.inserted_copy_rows` (`CopyInsertFits`),
and `PlainInsertRows`'s `LiteralData.inserted_plain`/`LiteralData.newCells_getElem?_of_plain`; the `NormalizedField` owners were deleted.

Surface consumers under [Belay/Sqlite](../packages/belay/Belay/Sqlite): `AggregateQuery`, `ColumnQuery`, `CountQuery`,
`FilteredDuplicateKeyQuery`, `ExistsQuery`, `NotExistsQuery`, `SelectOneFrom`, `SelectOneMayFail`, `UniqueLookupQuery`.
D1 removed `FilteredDuplicateKeyEmpty`; the three baseline filtered endpoints are replaced by
`Script.outputOn_noDuplicateKeysWhere` in `FilteredDuplicateKeyQuery`. The frozen endpoint inventory retains their names.
Coordinate with query migration; relocation need not rename a theorem. Keep no aliases.
Preserve public aggregation in [Belay.Sqlite.Model](../packages/belay-sqlite-model/Belay/Sqlite/Model.lean).

## Narrow three surface imports

These unchanged module bodies remain fixed targets. Proposed roots were compiled
at `3fe5caef` by [imports.py](../experiments/proof-boundaries/imports.py); revalidate
against current dependencies. Keep the rest of each body and its other imports.

| Surface module | Replace the `Belay.Sqlite.Model` umbrella with model roots | Preserve |
| --- | --- | --- |
| [Values.lean][values] | `Comparison`, `Declarations`, `StoreValue`, `StoreValueLaws`, `Truth` | All exported model names, literal/coercion instances and checked documentation. |
| [Script.lean][script] | `Declarations`, `Resolution.Syntax`, `SqlAdvance` | `Script`, `Script.empty`, append instance/laws, `Script.withValues`, `Script.withValues_statements`. |
| [ValueDisplay.lean][display] | `Declarations`, `OutputRepr` | `ToString Value`, `unexpandIntegerValue` and its `app_unexpander` registration; retain the Lean delaborator import. |

Rebuild downstream clients that may have relied on transitive umbrella names.
Historical `3fe5caef` closures were 580→75, 580→142 and 580→148 respectively;
they are not measurements of `3e2212ed`, timing claims or permanent CI thresholds.

## Explicitly deferred row-engine targets

These unchanged contracts stay specialized; unrelated ADR 0025 work can continue.

| Current owner | Deferred shared-interface replacement targets |
| --- | --- |
| [RowEngineTriggers.lean][row-triggers] | `NestedRun.Keeps`, `ProgramResult.Holds`; `raiseEffect_holds`, `runStep_holds`, `enterProgram_holds`, `runProgram_holds`, `runPrograms_holds` |
| [ForeignKeyCounterTriggers.lean][fk-triggers] | `raiseEffect_foreignKeyInvariant`, `runStep_counterBound`, `enterProgram_counterBound`, `runProgram_counterBound`, `runPrograms_counterBound` |
| [ForeignKeyWorkConditions.lean][work-conditions] | `ForeignKeyUpdateConditions`, `RowWork.ForeignKeySafe`, `Resolved.Step.ForeignKeySafe`, `ProgramsForeignKeySafe`, `ActionsForeignKeySafe`, `NestedRun.ForeignKeyKeeps`, `NestedRun.BeforeUpdateFrame` |
| [ForeignKeyEngineFacts.lean][engine-facts] | `Database.ForeignKeyReady`, `KeyState.ForeignKeyInvariant`, `KeyStop.ForeignKeyInvariant` retain their separate state/stop contracts. |
| [RowEngineWrites.lean][row-writes]; [ForeignKeyCounterRows.lean][fk-rows] | `runRows_holds`; `runRows_foreignKeyKeeps` fuel inductions were not generalized by either prototype. |
| [ForeignKeyCounterDelete.lean][fk-delete] | `deleteRow_counterBound` retains its combined check/removal phase; no per-micro-operation invariant is introduced. |

Keep the ten trigger proofs and consumers. FAIL retains the FK bound; rollback
requires database facts only; raw errors/undescribed stops impose no state fact.
Work permission and BEFORE UPDATE frames remain independent. Add no `RowKeeps`,
`StepAllowed` or narrow wrappers to production; the [Row experiments](../experiments/proof-boundaries/row-engine-findings.md)
are historical evidence, with no obligation to port their tests.

## Acceptance and test lifetime

Use the specification's checks; this inventory creates no checker or CI snapshot.
Keep unique witness coverage until clients/regressions supply it; retire redundant
witnesses after final Nix acceptance and record retirement in the existing status.

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
[cell-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AdmittedCellLaws.lean
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
