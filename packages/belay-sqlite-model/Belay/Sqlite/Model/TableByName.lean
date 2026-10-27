import Belay.Sqlite.Model.TableSourceLaws
import Belay.Sqlite.Model.ForeignKeyDropFrame
import Belay.Sqlite.Model.CatalogValidDrop
import Belay.Sqlite.Model.DatabaseLaws

set_option doc.verso true

/-! Tables found by name (ADR 0017, S6). A statement names a table, and the position of the table in
the catalog changes when an earlier object is dropped. A fact that has to survive such a change is
stated for the table that the name finds in each database, with the position that the lookup gives.
This module defines that lookup and shows that appending an object and dropping other objects keep
the table found by a name, with its rows. -/

namespace Belay.Sqlite.Model

/-- The table that a name finds in the database, with its catalog position: the first table, view or
index of that name in the catalog ({name}`Catalog.findTable`), when it is a table, with its stored rows.
For example, after {lit}`DROP TABLE customers` the name {lit}`sessions` finds the same table at position 0
instead of 1. -/
def Database.tableNamed (database : Database) (name : Identifier) : Option (Nat × Table) :=
  (database.catalog.findTable name).bind fun (position, _) => (database.table position).map (position, ·)

/-- For every database, name, position and catalog table that the lookup of the catalog finds: the name
finds the table of the database at that position, the catalog table with the stored rows of the position.
Proof sketch: unfold the lookup. -/
theorem Database.tableNamed_of_findTable {database : Database} {name : Identifier} {position : Nat}
    {shape : CatalogTable} (found : database.catalog.findTable name = some (position, shape)) :
    database.tableNamed name = (database.table position).map (position, ·) := by
  simp [Database.tableNamed, found]

/-- For every database, name, position and table that the name finds: the lookup of the catalog finds the
definition of the table at that position, and the database has the table there. Proof sketch: unfold the
lookup; the table comes from the position that the catalog gives. -/
theorem Database.tableNamed_some {database : Database} {name : Identifier} {position : Nat} {table : Table}
    (found : database.tableNamed name = some (position, table)) :
    database.catalog.findTable name = some (position, table.shape) ∧ database.table position = some table := by
  unfold Database.tableNamed at found
  cases lookup : database.catalog.findTable name with
  | none => simp [lookup] at found
  | some pair =>
    obtain ⟨place, shape⟩ := pair
    simp only [lookup, Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨stored, present, rfl, rfl⟩ := found
    have shapeEq := Database.table_of_findTable database name place shape lookup
    rw [present] at shapeEq
    cases shapeEq
    exact ⟨by simp, present⟩

/-- For every database, positions and name: if the name finds a table at a position that the drop
keeps, the database after {name}`Database.drop` finds the same table, with the same rows, at the
transported position ({name}`keptBelow`). In plain words, dropping other objects moves the table but
keeps what it holds. Proof sketch: {name}`Catalog.findTable_drop_kept` and {name}`Database.table_drop_kept`. -/
theorem Database.tableNamed_drop_kept {database : Database} {positions : List Nat} {name : Identifier}
    {position : Nat} {table : Table} (found : database.tableNamed name = some (position, table))
    (kept : !positions.contains position) :
    (database.drop positions).tableNamed name = some (keptBelow positions position, table) := by
  obtain ⟨lookup, present⟩ := Database.tableNamed_some found
  have moved := Catalog.findTable_drop_kept lookup kept
  have same := Database.table_drop_kept database positions kept
  rw [present] at same
  rw [Database.tableNamed_of_findTable moved, same]
  rfl

/-- For every database, name, table, definition of a new table and name of it: if the name finds a table
in the database, the database after CREATE TABLE ({name}`Catalog.createTable` with an empty row list
appended) finds the same table, with the same rows, at the same position. In plain words, creating a table
does not disturb a table found by name. Proof sketch: {name}`Catalog.findTable_append_of_some` and
{name}`Database.table_createTable`. -/
theorem Database.tableNamed_createTable {database : Database} {name : Identifier} {position : Nat}
    {table : Table} (found : database.tableNamed name = some (position, table))
    (created : Identifier) (definition : CatalogTable) :
    ({ catalog := database.catalog.createTable created definition, rows := database.rows ++ [[]] } : Database).tableNamed
      name = some (position, table) := by
  obtain ⟨lookup, present⟩ := Database.tableNamed_some found
  have moved := Catalog.findTable_append_of_some [{ name := created, entry := .table definition }] lookup
  rw [Database.tableNamed_of_findTable (by exact moved), Database.table_createTable created definition present]
  rfl

/-- For every database, name, table found by the name and target position other than the table's: after
{name}`Database.setRows` at the target, the name finds the same table, with the same rows, at the same
position. In plain words, writing the rows of one table does not disturb a table found by another
position. Proof sketch: the catalog is unchanged, and {name}`Database.table_setRows_other` keeps the table at
the other position. -/
theorem Database.tableNamed_setRows_other {database : Database} {name : Identifier} {position : Nat} {table : Table}
    (found : database.tableNamed name = some (position, table)) {target : Nat} (rows : List Row)
    (other : position ≠ target) : (database.setRows target rows).tableNamed name = some (position, table) := by
  obtain ⟨lookup, present⟩ := Database.tableNamed_some found
  have moved : (database.setRows target rows).catalog.findTable name = some (position, table.shape) := lookup
  rw [Database.tableNamed_of_findTable moved, Database.table_setRows_other database rows other, present]
  rfl

end Belay.Sqlite.Model
