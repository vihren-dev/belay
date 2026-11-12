import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyDdlConditions
import Belay.Sqlite.Model.Tooling.Counterexamples.ForeignKeyAddColumn

set_option doc.verso true

/-! The laws of the schema statements for the mapping that the catalog selects, with the
conditions of {lit}`ForeignKeyDdlConditions`. Each is the law for an arbitrary mapping function
with its premises read from those conditions. -/

namespace Belay.Sqlite.Model

/-- For every ADD COLUMN statement and database with row references under the selected mapping:
if the database meets {name}`Database.AddColumnRowsCondition`, the database after the statement
has row references under its selected mapping. Other error carriers require nothing. Proof sketch:
the old selection is unchanged ({name}`Catalog.parentLink_addColumn`), and the law for an arbitrary
mapping function applies with the reads of {name}`Database.AddColumnReads.of_selected`. -/
theorem runStatement_addColumn_rowReferencesSelected (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (column : CatalogColumn) (refuses : Bool) {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (condition : database.AddColumnRowsCondition target column refuses) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies
      (fun after => after.RowReferencesHold after.catalog.foreignKeyMapping) :=
  runStatement_addColumn_rowReferences Catalog.foreignKeyMapping clock counters parameters target column refuses
    holds (fun table found => Database.AddColumnReads.of_selected database found (condition.wide table found)
      (condition.declared table found) (condition.below table.shape (Database.tableAt_of_table found)))
    (fun _ _ _ key _ => Catalog.parentLink_addColumn database.catalog target column key condition.below)
    condition.newKeys

end Belay.Sqlite.Model
