import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.ForeignKeyStatement
import Belay.Sqlite.Model.ScriptRunHolds

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every profile, the conditional statement preservation contract holds for the
row atom under each database's selected mapping, including CREATE, ADD COLUMN and DROP.
Proof sketch: specialize the statement row-reference theorem; the condition supplies each
reached statement's input facts. -/
theorem rowReferences_statementKeeps (profile : Profile) :
    StatementKeeps (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping)
      (fun statement database => statement.ForeignKeyRowsCondition profile database) :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds met => runStatement_rowReferences clock counters parameters statement holds met)
    (fun _ _ _ _ _ _ _ _ _ h => h)

/-- For any supplied mapping compatible with a database's parent schemas, row truth
under that mapping is equivalent to row truth under the catalog-selected mapping. Empty
child tables still require schema compatibility. Proof sketch: compatibility equates each
declared parent comparison; substitute it in both directions of the row fact. -/
theorem Database.ParentSchemasCompatible.rowReferences_iff_selected {database : Database} {mapping : ForeignKeyMapping}
    (compatible : database.ParentSchemasCompatible mapping) :
    database.RowReferencesHold mapping ↔ database.RowReferencesHold database.catalog.foreignKeyMapping := by
  constructor <;> intro holds position table found key declared row member
  all_goals
    have same := (compatible position table found key declared).2
    simpa only [ForeignKeyMapping.link, Catalog.foreignKeyMapping, same] using holds position table found key declared row member

/-- For every profile and supplied mapping, each statement that keeps the catalog
({name}`Resolved.Statement.KeepsParentSchema`) and meets the FK row condition preserves both
schema compatibility and row truth under that mapping on success and FAIL. A schema statement
changes the catalog, so a fixed mapping does not describe its result; use
{lit}`foreignKeyAtomsSelected_statementKeeps` for those.
Proof sketch: compatibility identifies the supplied and selected comparisons; apply the
individual row and schema laws, then transport the row fact back through compatibility. -/
theorem foreignKeyAtoms_statementKeeps (profile : Profile) (mapping : ForeignKeyMapping) :
    StatementKeeps (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping)
      (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) :=
  StatementKeeps.ofOwnRun (by
  intro clock counters parameters statement database holds condition result kept
  have schema := runStatement_parentSchemasCompatible mapping clock counters parameters statement holds.1
    condition.1 result kept
  have rows := runStatement_rowReferences clock counters parameters statement
    (holds.1.rowReferences_iff_selected.mp holds.2) condition.2 result kept
  exact ⟨schema, schema.rowReferences_iff_selected.mpr rows⟩)
    (fun _ _ _ _ _ _ _ _ _ h => h)

/-- For any supplied mapping, clock, counters, parameters and input satisfying both FK
atoms, a statement that keeps the catalog and meets the row condition preserves both atoms in success and partial
FAIL results. Other error carriers require nothing. Proof: apply the combined statement
contract, whose premises concern the input and allowed effects. -/
theorem runStatement_foreignKeyAtoms (profile : Profile) (mapping : ForeignKeyMapping) (clock : Int)
    (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (holds : database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping)
    (condition : statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun result => result.ParentSchemasCompatible mapping ∧ result.RowReferencesHold mapping) :=
  foreignKeyAtoms_statementKeeps profile mapping clock counters parameters statement database holds condition _
    (StatementRun.effect_mem_effects _)

end Belay.Sqlite.Model
