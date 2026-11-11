import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyAddColumnDatabase
import Belay.Sqlite.Model.Schema.Columns.RowLocalAddColumn

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameter list, target, column and database: if the statement
refuses a populated table ({name}`Resolved.Statement.addColumn` with the flag set), and the database
has a table with at least one row at the target, the database of the effect of {name}`step` is the
database. Proof sketch: the refusal is the first check of the step for a table at the target. -/
theorem step_addColumn_refused_populated (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (column : CatalogColumn) (database : Database) {table : Table}
    (found : database.table target = some table) (populated : table.rows ≠ []) :
    effectDatabase (step clock counters parameters (.addColumn target column true) database) = database := by
  simp [step, found, effectDatabase, populated]

/-- For every clock value, counters, parameter list, target, column, flag and database: every success
or constraint failure of ADD COLUMN gives the database, or {name}`Database.addColumn` of an added
cell ({name}`AddedCell`) at a target that holds a table, and a table with rows is not the table of
a refusal. Proof sketch: {name}`step_addColumn_cases` gives the two shapes, and a refusing statement
on a table with rows keeps the database ({name}`step_addColumn_refused_populated`). -/
theorem runStatement_addColumn_cases (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (column : CatalogColumn) (refuses : Bool) (database : Database) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies
      (fun after => after = database ∨ ∃ table value, database.table target = some table ∧
        AddedCell table column value ∧ (refuses = true → table.rows = []) ∧
        after = database.addColumn target column value) := by
  simp only [runStatement]
  apply Effect.satisfies_of_effectDatabase
  rcases step_addColumn_cases clock counters parameters target column refuses database with
    kept | ⟨table, value, found, added, eq⟩
  · exact .inl kept
  · by_cases refused : refuses = true ∧ table.rows ≠ []
    · obtain ⟨rfl, populated⟩ := refused
      exact .inl (step_addColumn_refused_populated clock counters parameters target column database found populated)
    · refine .inr ⟨table, value, found, added, fun flagged => ?_, eq⟩
      exact Classical.byContradiction fun populated => refused ⟨flagged, populated⟩

/-- For any catalog-dependent mapping, an ADD COLUMN statement preserves parent-schema
compatibility if the input has it, the mapping of the catalog with the column agrees on every old
declaration, the catalog with the column selects the same parent link for every old declaration, and
every declaration of the new column has a located parent equal to the selection of the catalog with the
column. The last premise is empty for a column without {lit}`REFERENCES`. Stored rows are not read.
Other error carriers require nothing. Proof sketch: {name}`runStatement_addColumn_cases` and
{name}`Database.ParentSchemasCompatible.addColumn`. -/
theorem runStatement_addColumn_parentSchemasCompatible (mapping : Catalog → ForeignKeyMapping)
    (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (column : CatalogColumn)
    (refuses : Bool) {database : Database}
    (holds : database.ParentSchemasCompatible (mapping database.catalog))
    (same : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (mapping (database.catalog.addColumn target column)).parent position key =
        (mapping database.catalog).parent position key)
    (selection : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (database.catalog.addColumn target column).parentLink key = database.catalog.parentLink key)
    (newKeys : ∀ table, database.table target = some table → ∀ key ∈ column.foreignKeys,
      ((mapping (database.catalog.addColumn target column)).parent target key).isLocated = true ∧
        (mapping (database.catalog.addColumn target column)).parent target key =
          (database.catalog.addColumn target column).parentLink key) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible (mapping after.catalog)) := by
  intro after kept
  rcases runStatement_addColumn_cases clock counters parameters target column refuses database after kept with
    rfl | ⟨table, value, found, _, _, rfl⟩
  · exact holds
  · exact Database.ParentSchemasCompatible.addColumn holds found column value same selection (newKeys table found)

end Belay.Sqlite.Model
