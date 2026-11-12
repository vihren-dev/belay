import Belay

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Two schema conditions that the run laws keep, with the statement that breaks an atom without it.
A new index can change which parent key a declaration selects, and then it changes which child
columns the row atom tests for NULL. This is why the row laws for CREATE need the condition that every
old declaration keeps its selected parent ({lit}`Catalog.CreateKeepsSelection`). The same two statements
give the same results in SQLite 3.51.0: the second index makes {lit}`foreign_key_check` report the child.
A new column that references an absent table has no located parent, which breaks the schema atom
({lit}`Catalog.AddColumnLocatesNewKeys`) and leaves the row atom true. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyDdlNecessityFixture

/-- The parent has no index. The child row has a NULL in {lit}`y`, which exempts it while the
parent key is missing: the row atom tests the declared columns {lit}`(x, y)`. -/
def unindexed : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(a,b); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));
  INSERT INTO c VALUES(99,NULL);"

/-- The row atom holds and the schema atom fails: the parent has no key to select. -/
theorem startsMismatched : unindexed.raw.RowReferencesHold unindexed.raw.catalog.foreignKeyMapping ∧
    ¬ unindexed.raw.ParentSchemasCompatible unindexed.raw.catalog.foreignKeyMapping := by decide +kernel

/-- An index over {lit}`(a, b)` selects the pairs {lit}`(x, a)` and {lit}`(y, b)`. The child row
keeps its NULL in {lit}`y`, so it stays exempt and the row atom holds. -/
theorem pairedIndexKeepsRows : let script : Script := sql r"CREATE UNIQUE INDEX i ON p(a,b);"
    let result := unindexed.raw.run script
    result.outputs = [.done 0] ∧
    result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- An index over {lit}`(a, a)` also matches the key. It selects the child column {lit}`x` twice
and never reads {lit}`y`, so the row {lit}`(99, NULL)` has the non-NULL key 99 without a parent
row: the statement succeeds and the row atom fails. -/
theorem repeatedIndexBreaksRows : let script : Script := sql r"CREATE UNIQUE INDEX i ON p(a,a);"
    let result := unindexed.raw.run script
    result.outputs = [.done 0] ∧
    ¬ result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- The catalog after the second index. -/
def repeatedCatalog : Catalog :=
  (unindexed.raw.run (sql r"CREATE UNIQUE INDEX i ON p(a,a);")).connection.state.database.catalog

/-- The second index is the one object that the statement appends to the catalog. -/
theorem repeatedAppends : repeatedCatalog.length = unindexed.raw.catalog.length + 1 ∧
    repeatedCatalog.take unindexed.raw.catalog.length = unindexed.raw.catalog := by decide +kernel

/-- The shape of the child table. -/
def childShape : CatalogTable := (unindexed.raw.catalog.tableAt 1).getD {columns := []}

/-- The appended object does not meet the condition of the row laws: the declaration of the child
selects a different parent key with it. The general laws keep the condition for this reason. -/
theorem repeatedIndexNotKept (object : CatalogObject) (appended : repeatedCatalog = unindexed.raw.catalog ++ [object]) :
    ¬ unindexed.raw.catalog.CreateKeepsSelection object := by
  intro keeps
  have child : unindexed.raw.catalog.tableAt 1 = some childShape := by decide +kernel
  have all : ∀ key ∈ childShape.allForeignKeys, repeatedCatalog.parentLink key = unindexed.raw.catalog.parentLink key :=
    fun key member => by rw [appended]; exact keeps 1 childShape child key member
  revert all
  decide +kernel

/-- The child has a NULL key and a parent table that exists. -/
def parented : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k)); INSERT INTO c VALUES(NULL);"

/-- ADD COLUMN of a column that references a table that does not exist succeeds, as in SQLite. The
child rows keep row truth, because the new cell is NULL, but the new declaration has no parent
to select, so the schema atom fails. -/
theorem absentParentBreaksSchema : let script : Script := sql r"ALTER TABLE c ADD COLUMN w REFERENCES missing(k);"
    let result := parented.raw.run script
    result.outputs = [.done 0] ∧
    result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping ∧
    ¬ result.connection.state.database.ParentSchemasCompatible result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

end ForeignKeyDdlNecessityFixture

#print axioms ForeignKeyDdlNecessityFixture.startsMismatched
#print axioms ForeignKeyDdlNecessityFixture.pairedIndexKeepsRows
#print axioms ForeignKeyDdlNecessityFixture.repeatedIndexBreaksRows
#print axioms ForeignKeyDdlNecessityFixture.repeatedAppends
#print axioms ForeignKeyDdlNecessityFixture.repeatedIndexNotKept
#print axioms ForeignKeyDdlNecessityFixture.absentParentBreaksSchema
