import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyDdlConditions
import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeyAddColumn

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every ADD COLUMN statement and database with compatible parent schemas under the selected
mapping: if every old declaration keeps its selected parent ({name}`Catalog.AddColumnKeepsSelection`)
and every declaration of the column has a located parent ({name}`Catalog.AddColumnLocatesNewKeys`),
the database after the statement has compatible parent schemas under its selected mapping. Other
error carriers require nothing. Proof sketch: the law for an arbitrary mapping function, where the
new mapping is the new selection by definition. -/
theorem runStatement_addColumn_parentSchemasCompatibleSelected (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (column : CatalogColumn) (refuses : Bool) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (kept : database.catalog.AddColumnKeepsSelection target column)
    (locates : database.catalog.AddColumnLocatesNewKeys target column) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping) :=
  let selection := fun position table found key declared =>
    kept position table.shape (Database.tableAt_of_table found) key declared
  runStatement_addColumn_parentSchemasCompatible Catalog.foreignKeyMapping clock counters parameters target column
    refuses holds selection selection fun _ _ key declared => ⟨locates key declared, rfl⟩

end Belay.Sqlite.Model
