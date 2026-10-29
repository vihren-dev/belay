import Belay.Sqlite.Model.RowEngineFacts
import Belay.Sqlite.Model.DropColumnCellLaws
import Belay.Sqlite.Model.EffectSatisfies

set_option doc.verso true

/-! Shared table frame evidence and database update facts, below invariant instances. -/

namespace Belay.Sqlite.Model

/-- For the given property of a table and database: the property holds for every table of the
database. For {name}`Table.NotNull` this is {name}`Database.NotNull`, and other table properties use the same quantification. -/
abbrev Database.EachTable (database : Database) (atom : Table → Prop) : Prop :=
  database.EveryTable fun _ table => atom table

/-- The shared frame contract of a table property. For each table, the following facts hold:
* a table without rows has it (CREATE TABLE stores such a table);
* a table with the same catalog entry as a table that has it, and a sublist of its rows, has it
  (DELETE stores such a table);
* a table with the same rows as a table that has it, and a shape that differs only in names
  ({lit}`CatalogTable.blankNames`), has it (a rename stores such a table);
* a table that has it and can lose a column cleanly still has it without the column (DROP COLUMN stores such a table).

Use {lit}`Table.rowidsDistinctAtom` for distinct rowids. Row-local constraint evidence extends this contract. -/
structure TableAtom (atom : Table → Prop) : Prop where
  /-- A table without rows has the property. -/
  empty : ∀ table, table.rows = [] → atom table
  /-- A table with the same entry and a sublist of the rows of a table that has the property has
  it. -/
  sublist : ∀ table other, atom table → other.shape = table.shape → other.rows.Sublist table.rows → atom other
  /-- A table with the same rows and a shape with the same names blanked
  ({lit}`CatalogTable.blankNames`) as a table that has the property has it. -/
  renamed : ∀ table other, atom table → other.rows = table.rows →
    table.shape.blankNames = other.shape.blankNames → atom other
  /-- A table that can lose a column ({lit}`CatalogTable.DropsCleanly`) and has the property still has it after
  the drop ({lit}`Table.dropColumn`): a DROP COLUMN stores such a table. -/
  dropped : ∀ table index, atom table → table.shape.DropsCleanly index → atom (table.dropColumn index)

/-- For every atom, database, position, table and rows: if every table of the database has the
atom, the database has the table at the position, and the table with the rows has the atom, then
every table of the database after {name}`Database.setRows` with the rows at the position has it.
Proof sketch: {name}`Database.Every.setRows` with a fact that ignores catalog and position.
Its out-of-range case needs no assumption about the number of row lists. -/
theorem Database.EachTable.setRows {atom : Table → Prop} {database : Database} (every : database.EachTable atom)
    {target : Nat} {table : Table} (found : database.table target = some table) {rows : List Row}
    (stored : atom { table with rows }) : (database.setRows target rows).EachTable atom :=
  Database.Every.setRows (fact := fun _ _ table => atom table) every found stored

/-- For every database whose row lists match its catalog, object and position: the table at the
position after the object and an empty row list are appended is the table at the position
before, or a table without rows. Proof sketch: a position below the old catalog length sees the
old catalog entry and row list; every other position reads the appended empty row list or the
default. -/
theorem Database.table_append_cases {database : Database} (aligned : database.rows.length = database.catalog.length)
    (object : CatalogObject) {position : Nat} {table : Table}
    (present : ({ catalog := database.catalog ++ [object], rows := database.rows ++ [[]] } : Database).table position =
      some table) :
    database.table position = some table ∨ table.rows = [] := by
  by_cases below : position < database.catalog.length
  · refine .inl ?_
    unfold Database.table Catalog.tableAt at present ⊢
    rw [List.getElem?_append_left below, rows_getD_append_nil] at present
    exact present
  · refine .inr ?_
    unfold Database.table at present
    obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp present
    rw [← same]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
    split
    · omega
    · rename_i _ beyond
      cases rest : position - database.rows.length with
      | zero => simp
      | succ _ => simp

/-- For every atom, database and object whose row lists match its catalog: if the atom is a
{name}`TableAtom` and every table of the database has it, every table of the database with the
object and an empty row list appended has it. Proof sketch: a table of the new database is a table
of the old one or has no rows ({name}`Database.table_append_cases`). -/
theorem Database.EachTable.appendEmpty {atom : Table → Prop} (tableAtom : TableAtom atom) {database : Database}
    (every : database.EachTable atom) (aligned : database.rows.length = database.catalog.length)
    (object : CatalogObject) :
    ({ catalog := database.catalog ++ [object], rows := database.rows ++ [[]] } : Database).EachTable atom := by
  intro position table present
  rcases Database.table_append_cases aligned object present with old | empty
  · exact every position table old
  · exact tableAtom.empty table empty

end Belay.Sqlite.Model
