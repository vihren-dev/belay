import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.ForeignKeyDdlConditions

set_option doc.verso true

/-! The laws of the schema statements for the mapping that the catalog selects, with the
conditions of {lit}`ForeignKeyDdlConditions`. Each is the law for an arbitrary mapping function
with its premises read from those conditions. -/

namespace Belay.Sqlite.Model

/-- For every CREATE statement of an object, clock, counters, parameters and database with row
references under the selected mapping: if every old declaration keeps its selected parent
({name}`Catalog.CreateKeepsSelection`), the database after the statement has row references under
its selected mapping. Other error carriers require nothing. Proof sketch: the law for an
arbitrary mapping function, where the mapping function reads the parent link of the catalog. -/
theorem runStatement_create_rowReferencesSelected (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database} (object : CatalogObject)
    (creates : statement.CreatesObject object)
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (kept : database.catalog.CreateKeepsSelection object) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.RowReferencesHold after.catalog.foreignKeyMapping) :=
  runStatement_create_rowReferences Catalog.foreignKeyMapping clock counters parameters statement object creates
    holds fun _ table found key declared => kept _ table.shape (Database.tableAt_of_table found) key declared

/-- For every CREATE statement of an object, clock, counters, parameters and database with
compatible parent schemas under the selected mapping: if every old declaration keeps its selected
parent ({name}`Catalog.CreateKeepsSelection`) and every declaration of a new table has a located
parent ({name}`Catalog.CreateLocatesNewKeys`), the database after the statement has compatible parent
schemas under its selected mapping. Other error carriers require nothing. Proof sketch: the law for
an arbitrary mapping function, where the new mapping is the new selection by definition. -/
theorem runStatement_create_parentSchemasCompatibleSelected (clock : Int) (counters : Counters)
    (parameters : List Value) (statement : Resolved.Statement) {database : Database} (object : CatalogObject)
    (creates : statement.CreatesObject object)
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (kept : database.catalog.CreateKeepsSelection object) (locates : database.catalog.CreateLocatesNewKeys object) :
    (runStatement clock counters parameters statement database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping) :=
  let selection := fun position table found key declared =>
    kept position table.shape (Database.tableAt_of_table found) key declared
  runStatement_create_parentSchemasCompatible Catalog.foreignKeyMapping clock counters parameters statement object
    creates holds selection selection fun shape entry key declared => ⟨locates shape entry key declared, rfl⟩

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

/-- For every plain DROP and database with row references under the selected mapping: if every kept
declaration keeps its selected parent, moved to the kept positions
({name}`Catalog.DropKeepsSelection`), and every located parent of it is kept
({name}`Catalog.DropKeepsParents`), the database after the statement has row references under
its selected mapping. Other error carriers require nothing. Proof sketch: the law for an arbitrary
mapping function, where the mapping reads the parent link. -/
theorem runStatement_drop_rowReferencesSelected (clock : Int) (counters : Counters) (parameters : List Value)
    (positions : List Nat) {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (moved : database.catalog.DropKeepsSelection positions) (parents : database.catalog.DropKeepsParents positions) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies
      (fun after => after.RowReferencesHold after.catalog.foreignKeyMapping) :=
  runStatement_drop_rowReferences Catalog.foreignKeyMapping clock counters parameters positions holds
    (fun child table found kept key declared => moved child table.shape (Database.tableAt_of_table found) kept key declared)
    (fun child table found kept key declared => parents child table.shape (Database.tableAt_of_table found) kept key declared)

/-- For every DROP, with or without rules, and database with compatible parent schemas under the
selected mapping: if every kept declaration keeps its selected parent, moved to the kept positions
({name}`Catalog.DropKeepsSelection`), the database after the statement has compatible parent schemas
under its selected mapping. Other error carriers require nothing. Proof sketch: the laws for an
arbitrary mapping function, where the mapping reads the parent link. -/
theorem runStatement_drop_parentSchemasCompatibleSelected (clock : Int) (counters : Counters)
    (parameters : List Value) (positions : List Nat) (rules : Option Resolved.WriteRules) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (moved : database.catalog.DropKeepsSelection positions) :
    (runStatement clock counters parameters (.drop positions rules) database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping) := by
  cases rules with
  | none =>
    exact runStatement_drop_parentSchemasCompatible Catalog.foreignKeyMapping clock counters parameters positions
      holds (fun child table found kept key declared => moved child table.shape (Database.tableAt_of_table found) kept key declared)
      fun child table found kept key declared => moved child table.shape (Database.tableAt_of_table found) kept key declared
  | some rules =>
    exact runStatement_drop_enforced_parentSchemasCompatible Catalog.foreignKeyMapping rules clock counters parameters
      positions holds moved moved

end Belay.Sqlite.Model
