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
  fun clock counters parameters statement _ holds met => runStatement_rowReferences clock counters parameters statement holds met

/-- For every resolved script, starting position and state, if the current database and
any saved snapshot have selected row references, and each reached statement meets its FK
conditions, every retained outcome database has selected references. This includes FAIL,
rollback and both databases of a pending transaction. Unreached suffixes require nothing.
Proof sketch: apply the existing snapshot-aware SQL invariant theorem. -/
theorem runSqlFrom_rowReferences (profile : Profile) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeyRowsCondition profile database) position script state) :
    (runSqlFrom position script state).Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runSqlFrom_holds (rowReferences_statementKeeps profile) position script holds conditions

/-- For any fresh resolved script and input with selected row references, all retained
outcome databases have the row fact when each reached statement meets its FK conditions.
A fresh run has no saved-snapshot entry premise. Proof: specialize the SQL invariant law. -/
theorem runSql_rowReferences (profile : Profile) (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeyRowsCondition profile database) 0 script {database}) :
    (runSql script database).Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runSql_holds (rowReferences_statementKeeps profile) script holds conditions

/-- For any surface script, resolution context, clock and connection, selected row
references hold in the final database and snapshot if they hold in both initial stores and
each reached resolved statement meets its FK conditions. Failed resolution and halted
suffixes impose no extra condition. Proof: apply the existing surface-run invariant law. -/
theorem runScriptFrom_rowReferences (profile : Profile) (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : ScriptConditionsWith (fun statement database => statement.ForeignKeyRowsCondition profile database)
      context clock index connection script) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runScriptFrom_holds (rowReferences_statementKeeps profile) context clock index script holds conditions

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
      (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) := by
  intro clock counters parameters statement database holds condition result kept
  have schema := runStatement_parentSchemasCompatible mapping clock counters parameters statement holds.1
    condition.1 result kept
  have rows := runStatement_rowReferences clock counters parameters statement
    (holds.1.rowReferences_iff_selected.mp holds.2) condition.2 result kept
  exact ⟨schema, schema.rowReferences_iff_selected.mpr rows⟩

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
  foreignKeyAtoms_statementKeeps profile mapping clock counters parameters statement database holds condition

/-- For any supplied mapping and resolved script, if both FK atoms hold on the current
database and saved snapshot, and each reached statement keeps the catalog and meets its row
condition, both atoms hold on every retained outcome database, including rollback and pending snapshots.
Proof sketch: apply the existing SQL invariant theorem to the conjunction. -/
theorem runSqlFrom_foreignKeyAtoms (profile : Profile) (mapping : ForeignKeyMapping) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping))
    (conditions : RunConditionsWith (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) position script state) :
    (runSqlFrom position script state).Holds
      (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runSqlFrom_holds (foreignKeyAtoms_statementKeeps profile mapping) position script holds conditions

/-- For any supplied mapping and fresh resolved script, both FK atoms on the input and
the reached statements, each keeping the catalog and meeting its row condition, imply both atoms on every retained outcome database.
No initial snapshot is present. Proof: specialize the conjunction's SQL invariant law. -/
theorem runSql_foreignKeyAtoms (profile : Profile) (mapping : ForeignKeyMapping)
    (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping)
    (conditions : RunConditionsWith (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) 0 script {database}) :
    (runSql script database).Holds
      (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runSql_holds (foreignKeyAtoms_statementKeeps profile mapping) script holds conditions

/-- For any supplied mapping and surface script, both FK atoms hold in the final current
database and snapshot when they hold in both initial stores and each reached resolved
statement keeps the catalog and meets its row condition. Failed resolution and unreached
suffixes add no premise.
Proof sketch: apply the existing surface-run invariant law to the conjunction. -/
theorem runScriptFrom_foreignKeyAtoms (profile : Profile) (mapping : ForeignKeyMapping) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping))
    (conditions : ScriptConditionsWith (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database)
      context clock index connection script) :
    (runScriptFrom context clock index connection script).connection.state.Holds
      (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runScriptFrom_holds (foreignKeyAtoms_statementKeeps profile mapping) context clock index script holds conditions

end Belay.Sqlite.Model
