import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.ForeignKeyAddColumnDatabase
import Belay.Sqlite.Model.RowLocalAddColumn

set_option doc.verso true

/-! Foreign-key atoms through the ADD COLUMN statement, with separate row-mapping and
parent-selection premises. A refused or failed addition keeps the database; a success appends one
cell to each row of the target table and the declarations of the column to the table. -/

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

/-- For any mapping selected as a function of the catalog, an ADD COLUMN statement preserves row
references if the input has them and:
* the rows of the target are wide and the mapping reads only columns of the table
  ({name}`Database.AddColumnReads`);
* the mapping of the catalog with the column agrees on every old declaration;
* for each added cell, a statement that refuses a populated table needs no further fact, and every
  declaration of the new column is satisfied by each old row with the cell appended.
A refused or failed addition keeps the database. Other error carriers require nothing. Proof
sketch: {name}`runStatement_addColumn_cases` and {name}`Database.RowReferencesHold.addColumn`. -/
theorem runStatement_addColumn_rowReferences (mapping : Catalog → ForeignKeyMapping)
    (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (column : CatalogColumn)
    (refuses : Bool) {database : Database}
    (holds : database.RowReferencesHold (mapping database.catalog))
    (reads : ∀ table, database.table target = some table → database.AddColumnReads (mapping database.catalog) target table)
    (same : ∀ position table, database.table position = some table → ∀ key ∈ table.shape.allForeignKeys,
      (mapping (database.catalog.addColumn target column)).parent position key =
        (mapping database.catalog).parent position key)
    (newKeys : ∀ table value, database.table target = some table → AddedCell table column value →
      (refuses = true → table.rows = []) → ∀ key ∈ column.foreignKeys, ∀ row ∈ table.rows,
        ((mapping (database.catalog.addColumn target column)).link target key).satisfied
          (database.addColumn target column value) (row.appendValues [Value.store column.affinity value]) = true) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies
      (fun after => after.RowReferencesHold (mapping after.catalog)) := by
  intro after kept
  rcases runStatement_addColumn_cases clock counters parameters target column refuses database after kept with
    rfl | ⟨table, value, found, added, flagged, rfl⟩
  · exact holds
  · exact Database.RowReferencesHold.addColumn holds found (reads table found) column value same
      (newKeys table value found added flagged)

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

/-- For any ADD COLUMN statement, both FK atoms under the catalog-selected mapping survive when
both hold initially and:
* the rows of the target are wide ({name}`Database.RowsWideAt`) and the declarations of the target
  name only its columns ({name}`Database.DeclarationsBelowAt`);
* the target table selects its parents below its width ({name}`Database.SelectionBelowAt`), so
  the new column changes no old selection and no selected parent key reads it;
* every declaration of the new column has a located parent in the catalog with the column;
* for each added cell, a statement that refuses a populated table needs no further fact, and every
  declaration of the new column is satisfied by each old row with the cell appended.
A column without {lit}`REFERENCES` has no obligation in the last two items. Other error carriers
require nothing. Proof sketch: the selection of every old declaration is unchanged
({name}`Catalog.parentLink_addColumn`), so the mapping of the catalog with the column agrees with the
old one; then apply the separate row and schema ADD COLUMN laws. -/
theorem runStatement_addColumn_foreignKeyAtoms (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (column : CatalogColumn) (refuses : Bool) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (wide : database.RowsWideAt target) (declared : database.DeclarationsBelowAt target)
    (below : database.SelectionBelowAt target)
    (locatedKeys : ∀ key ∈ column.foreignKeys, ((database.catalog.addColumn target column).parentLink key).isLocated = true)
    (newKeys : ∀ table value, database.table target = some table → AddedCell table column value →
      (refuses = true → table.rows = []) → ∀ key ∈ column.foreignKeys, ∀ row ∈ table.rows,
        ((database.catalog.addColumn target column).foreignKeyMapping.link target key).satisfied
          (database.addColumn target column value) (row.appendValues [Value.store column.affinity value]) = true) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping ∧
        after.RowReferencesHold after.catalog.foreignKeyMapping) := by
  have selection : ∀ position table, database.table position = some table →
      ∀ key ∈ table.shape.allForeignKeys,
        (database.catalog.addColumn target column).parentLink key = database.catalog.parentLink key :=
    fun _ _ _ key _ => Catalog.parentLink_addColumn database.catalog target column key below
  intro after kept
  exact ⟨runStatement_addColumn_parentSchemasCompatible Catalog.foreignKeyMapping clock counters parameters target
      column refuses holds.1 (fun position table found key declared => selection position table found key declared)
      selection (fun _ _ key declared => ⟨locatedKeys key declared, rfl⟩) after kept,
    runStatement_addColumn_rowReferences Catalog.foreignKeyMapping clock counters parameters target column refuses
      holds.2 (fun table found => Database.AddColumnReads.of_selected database found (wide table found)
        (declared table found) (below table.shape (Database.tableAt_of_table found)))
      (fun position table found key declared => selection position table found key declared) newKeys after kept⟩

end Belay.Sqlite.Model
