import Belay.Sqlite.Model.ForeignKeyCreateFrame
import Belay.Sqlite.Model.ForeignKeyCreateSelection
import Belay.Sqlite.Model.RowLocalFrame

set_option doc.verso true

/-! Foreign-key atoms through the four CREATE forms (table, view, index and trigger), with
separate row-mapping and parent-selection premises. The common frame follows actual statement
execution. -/

namespace Belay.Sqlite.Model

/-- The statement is CREATE TABLE, CREATE VIEW, CREATE INDEX or CREATE TRIGGER for exactly this
object. Its target position is unrestricted here; execution checks that it is the catalog end.
Every other statement fails this condition. Use this relation to share the append frame. -/
def Resolved.Statement.CreatesObject (statement : Resolved.Statement) (object : CatalogObject) : Prop :=
  match statement with
  | .createTable _ name shape => object = {name, entry := .table shape}
  | .createIndex _ name index => object = {name, entry := .index index}
  | .createTrigger _ name trigger => object = {name, entry := .trigger trigger}
  | .createView _ name view => object = {name, entry := .view view}
  | .addColumn .. | .drop .. | .insert .. | .upsert .. | .update .. | .delete ..
  | .query .. | .begin | .commit | .rollback | .prepareError .. | .setting .. => False

/-- For every CREATE statement with the specified object, clock, counters, parameters and
input, every success has aligned input storage and appends exactly the object and empty rows.
CREATE has no partial FAIL carrier; other errors require nothing. Proof sketch: inspect the
four CREATE branches and their existing end-position, storage and unique-index checks. -/
theorem runStatement_create_frame (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) (database : Database) (object : CatalogObject)
    (creates : statement.CreatesObject object) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => database.rows.length = database.catalog.length ∧
        after = {catalog := database.catalog ++ [object], rows := database.rows ++ [[]]}) := by
  cases statement with
  | createTable target name shape | createView target name shape | createTrigger target name shape =>
    change object = _ at creates
    subst object
    simp only [runStatement, step]
    split
    · rename_i fits
      simp only [Bool.and_eq_true, beq_iff_eq] at fits
      exact Effect.satisfies_of_effectDatabase ⟨fits.2, rfl⟩
    · intro after kept
      rcases kept with kept | kept <;> cases kept
  | createIndex target name index =>
    change object = _ at creates
    subst object
    simp only [runStatement, step]
    split
    · rename_i fits
      simp only [Bool.and_eq_true, beq_iff_eq] at fits
      split
      · intro after kept; rcases kept with kept | kept <;> cases kept
      · split
        · intro after kept; rcases kept with kept | kept <;> cases kept
        · exact Effect.satisfies_of_effectDatabase ⟨fits.2, rfl⟩
    · intro after kept; rcases kept with kept | kept <;> cases kept
  | addColumn | drop | insert | upsert | update | delete | query | begin | commit
  | rollback | prepareError | setting => exact False.elim creates

/-- For any mapping selected as a function of the catalog, a CREATE statement preserves
row references if the input has them and the extended mapping agrees on every old declaration.
New declarations have no rows, and no parent-key compatibility is assumed. Other error carriers
require nothing. Proof sketch: the CREATE frame exposes an aligned empty append, to which the
independent row-comparison frame applies. -/
theorem runStatement_create_rowReferences (mapping : Catalog → ForeignKeyMapping)
    (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (object : CatalogObject) (creates : statement.CreatesObject object)
    (holds : database.RowReferencesHold (mapping database.catalog))
    (same : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (mapping (database.catalog ++ [object])).parent position key = (mapping database.catalog).parent position key) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.RowReferencesHold (mapping after.catalog)) := by
  intro after kept
  obtain ⟨aligned, rfl⟩ := runStatement_create_frame clock counters parameters statement database object creates after kept
  exact holds.appendEmpty aligned object same

/-- For any catalog-dependent mapping, a CREATE statement preserves parent-schema
compatibility if the input has it, old declared mappings and selections are unchanged,
and every new declared key maps to a located parent selected by the extended catalog.
The new-key premise is empty for indexes, triggers and tables without keys. Other error
carriers require nothing. Proof sketch: use the CREATE frame and the schema append law. -/
theorem runStatement_create_parentSchemasCompatible (mapping : Catalog → ForeignKeyMapping)
    (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (object : CatalogObject) (creates : statement.CreatesObject object)
    (holds : database.ParentSchemasCompatible (mapping database.catalog))
    (same : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (mapping (database.catalog ++ [object])).parent position key = (mapping database.catalog).parent position key)
    (selection : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (database.catalog ++ [object]).parentLink key = database.catalog.parentLink key)
    (newKeys : ∀ shape, object.entry = .table shape → ∀ key ∈ shape.allForeignKeys,
      ((mapping (database.catalog ++ [object])).parent database.catalog.length key).isLocated = true ∧
      (mapping (database.catalog ++ [object])).parent database.catalog.length key =
        (database.catalog ++ [object]).parentLink key) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible (mapping after.catalog)) := by
  intro after kept
  obtain ⟨_, rfl⟩ := runStatement_create_frame clock counters parameters statement database object creates after kept
  exact holds.appendEmpty object same selection newKeys

/-- For any CREATE statement, both FK atoms under the catalog-selected mapping survive
when both hold initially and every new declared key has a located parent in the extended
catalog. Indexes, triggers and tables without foreign keys have no new-key obligation.
Other error carriers impose nothing. Proof sketch: input schema compatibility proves
old selection stability, then apply the separate row and schema CREATE laws. -/
theorem runStatement_create_foreignKeyAtoms (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database} (object : CatalogObject)
    (creates : statement.CreatesObject object)
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (newKeys : ∀ shape, object.entry = .table shape → ∀ key ∈ shape.allForeignKeys,
      ((database.catalog ++ [object]).parentLink key).isLocated = true) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping ∧
        after.RowReferencesHold after.catalog.foreignKeyMapping) := by
  have selection := holds.1.selection_append [object]
  intro after kept
  constructor
  · exact runStatement_create_parentSchemasCompatible Catalog.foreignKeyMapping clock counters parameters statement object creates
      holds.1 selection selection (fun shape entry key declared => ⟨newKeys shape entry key declared, rfl⟩) after kept
  · exact runStatement_create_rowReferences Catalog.foreignKeyMapping clock counters parameters statement object creates
      holds.2 selection after kept

end Belay.Sqlite.Model
