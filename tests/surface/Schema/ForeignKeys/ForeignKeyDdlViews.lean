import Belay

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! CREATE VIEW and DROP VIEW through the foreign-key laws. A view appends or removes one catalog
object and writes no rows. It changes the selected parent of a declaration only for a declaration
that names the view: the name of a parent that does not exist finds the view, and the link changes
from missing to mismatch ({lit}`Catalog.parentLink`). The row laws keep the condition that every old
declaration keeps its selected parent ({lit}`Catalog.CreateKeepsSelection`) for this reason. A view
with another name keeps both atoms, and the schema atom gives the condition when a declaration names
a view, because every selected parent of a database that has the atom is a table. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyDdlViewsFixture

/-- The child names a parent {lit}`v` that does not exist. Its row has a NULL key, so the row atom
holds, and the schema atom fails: the parent is missing. -/
def hanging : Belay.Sqlite.Database := db! r"
  CREATE TABLE c(x REFERENCES v(k)); INSERT INTO c VALUES(NULL);"

/-- The catalog after CREATE VIEW of the name that the child names. -/
def namedCatalog : Catalog :=
  (hanging.raw.run (sql r"CREATE VIEW v AS SELECT 1 AS k;")).connection.state.database.catalog

/-- The shape of the child table. -/
def childShape : CatalogTable := (hanging.raw.catalog.tableAt 0).getD {columns := []}

/-- The statement succeeds and appends the view. -/
theorem namedViewAppends : let result := hanging.raw.run (sql r"CREATE VIEW v AS SELECT 1 AS k;")
    result.outputs = [.done 0] ∧ namedCatalog.length = hanging.raw.catalog.length + 1 ∧
    namedCatalog.take hanging.raw.catalog.length = hanging.raw.catalog := by decide +kernel

/-- The view takes the name of the missing parent: the link of the declaration changes from missing
to a mismatch, as SQLite reports a view as a parent. -/
theorem namedViewChangesLink (key : ForeignKey) (member : key ∈ childShape.allForeignKeys) :
    hanging.raw.catalog.parentLink key = .missing ∧ namedCatalog.parentLink key = .mismatch 1 := by
  have all : ∀ key ∈ childShape.allForeignKeys, hanging.raw.catalog.parentLink key = .missing ∧
      namedCatalog.parentLink key = .mismatch 1 := by decide +kernel
  exact all key member

/-- The appended view does not meet the condition of the row laws. The general laws keep the
condition for this reason. -/
theorem namedViewNotKept (object : CatalogObject) (appended : namedCatalog = hanging.raw.catalog ++ [object]) :
    ¬ hanging.raw.catalog.CreateKeepsSelection object := by
  intro keeps
  have child : hanging.raw.catalog.tableAt 0 = some childShape := by decide +kernel
  have all : ∀ key ∈ childShape.allForeignKeys, namedCatalog.parentLink key = hanging.raw.catalog.parentLink key :=
    fun key member => by rw [appended]; exact keeps 0 childShape child key member
  revert all
  decide +kernel

/-- The parent exists, and the child row has a parent row. -/
def parented : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k)); INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- A view with another name keeps both atoms, and so does the same view after DROP VIEW. -/
theorem otherViewKeepsAtoms : let created := parented.raw.run (sql r"CREATE VIEW w AS SELECT k FROM p;")
    let dropped := parented.raw.run (sql r"CREATE VIEW w AS SELECT k FROM p; DROP VIEW w;")
    created.outputs = [.done 0] ∧
    created.connection.state.database.ParentSchemasCompatible created.connection.state.database.catalog.foreignKeyMapping ∧
    created.connection.state.database.RowReferencesHold created.connection.state.database.catalog.foreignKeyMapping ∧
    dropped.outputs = [.done 0, .done 0] ∧
    dropped.connection.state.database.ParentSchemasCompatible dropped.connection.state.database.catalog.foreignKeyMapping ∧
    dropped.connection.state.database.RowReferencesHold dropped.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- The child names a view as its parent. The row has a NULL key. -/
def viewParent : Belay.Sqlite.Database := db! r"
  CREATE VIEW v AS SELECT 1 AS k; CREATE TABLE c(x REFERENCES v(k)); INSERT INTO c VALUES(NULL);"

/-- The shape of the child table, which is at position 1. -/
def viewChildShape : CatalogTable := (viewParent.raw.catalog.tableAt 1).getD {columns := []}

/-- A view is a mismatch as a parent. After DROP VIEW the name finds nothing, and the link is missing. -/
theorem droppedViewMissesLink (key : ForeignKey) (member : key ∈ viewChildShape.allForeignKeys) :
    viewParent.raw.catalog.parentLink key = .mismatch 0 ∧ (viewParent.raw.catalog.drop [0]).parentLink key = .missing := by
  have all : ∀ key ∈ viewChildShape.allForeignKeys, viewParent.raw.catalog.parentLink key = .mismatch 0 ∧
      (viewParent.raw.catalog.drop [0]).parentLink key = .missing := by decide +kernel
  exact all key member

/-- The kept child declaration does not keep its selected parent, moved, so the DROP condition of the
row laws refuses this DROP VIEW. -/
theorem droppedViewNotKept : ¬ viewParent.raw.catalog.DropKeepsSelection [0] := by
  intro keeps
  have child : viewParent.raw.catalog.tableAt 1 = some viewChildShape := by decide +kernel
  have all : ∀ key ∈ viewChildShape.allForeignKeys, (viewParent.raw.catalog.drop [0]).parentLink key =
      (viewParent.raw.catalog.parentLink key).transport (keptBelow [0]) :=
    fun key member => keeps 1 viewChildShape child (by decide +kernel) key member
  revert all
  decide +kernel

end ForeignKeyDdlViewsFixture

#print axioms ForeignKeyDdlViewsFixture.namedViewAppends
#print axioms ForeignKeyDdlViewsFixture.namedViewChangesLink
#print axioms ForeignKeyDdlViewsFixture.namedViewNotKept
#print axioms ForeignKeyDdlViewsFixture.otherViewKeepsAtoms
#print axioms ForeignKeyDdlViewsFixture.droppedViewMissesLink
#print axioms ForeignKeyDdlViewsFixture.droppedViewNotKept
#print axioms Belay.Sqlite.Model.Catalog.parentLink_createView_of_other_name
#print axioms Belay.Sqlite.Model.Catalog.createKeepsSelection_view
