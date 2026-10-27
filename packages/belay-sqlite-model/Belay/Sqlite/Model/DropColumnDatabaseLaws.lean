import Belay.Sqlite.Model.DropColumnKeyLaws
import Belay.Sqlite.Model.OutlineKeyLaws
import Belay.Sqlite.Model.OutlineDatabaseLaws

set_option doc.verso true

/-! The tables of a database after ALTER TABLE DROP COLUMN (ADR 0019, D4). The database with the catalog
without the column ({lit}`Catalog.dropColumn`) and the rows without the cell has the table at the position
without its column ({lit}`Table.dropColumn`) and every other table as it was. The database that the run stores
has the catalog of the statement instead, which has the outline of that catalog, so a fact about the rows that
the outline keeps ({lit}`Database.EveryTable.of_outline`) passes from the one database to the other. -/

namespace Belay.Sqlite.Model

/-- For every rows, position, function and position of a list: the list at the position after the function was
mapped over the list at the changed position is the mapped list there and the same list elsewhere. Proof
sketch: {lit}`List.getElem?_modify`. -/
theorem rows_modify_getD (rows : List (List Row)) (position other : Nat) (change : List Row → List Row)
    (empty : change [] = []) :
    (rows.modify position change).getD other [] = if position = other then change (rows.getD other []) else rows.getD other [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify, List.getD_eq_getElem?_getD]
  by_cases same : position = other
  · cases rows[other]? <;> simp [same, empty]
  · cases rows[other]? <;> simp [same]

/-- For every database, position, index and table at the position: the table of the database with the catalog
after the drop and the rows without the cell ({name}`Database.dropColumn`) is, at the position, the table without
its column ({name}`Table.dropColumn`), and at every other position the table before. Proof sketch: the tables of
the catalog ({name}`Catalog.tableAt_dropColumn_same`, {name}`Catalog.tableAt_dropColumn_other`) and the rows
({name}`rows_modify_getD`). -/
theorem Database.table_dropColumn (database : Database) {position index : Nat} {shape : CatalogTable}
    (found : database.catalog.tableAt position = some shape) (other : Nat) :
    (database.dropColumn position index (database.catalog.dropColumn position index)).table other =
      if position = other then (database.table position).map (Table.dropColumn index) else database.table other := by
  unfold Database.table Database.dropColumn
  simp only
  rw [rows_modify_getD _ _ _ _ rfl]
  by_cases same : position = other
  · subst same
    simp [Catalog.tableAt_dropColumn_same found, found, Table.dropColumn]
  · simp [same, Catalog.tableAt_dropColumn_other _ index (Ne.symm same)]

/-- For every database, position, index and catalog that the model runs as a DROP COLUMN
({name}`Database.runsDropColumn`): the catalog has a table at the position that the column can leave, no index of
the catalog reads the column, and the catalog of the statement has the outline and the selected parents of the catalog
after the drop. Proof sketch: the two tests of the definition, {name}`Catalog.droppable_spec` and
{name}`Catalog.keepsOutline_eq`. -/
theorem Database.runsDropColumn_spec {database : Database} {position index : Nat} {stored : Catalog}
    (runs : database.runsDropColumn position index stored = true) :
    (∃ shape, database.catalog.tableAt position = some shape ∧ shape.DropsCleanly index ∧
      ∀ object ∈ database.catalog, ∀ definition, object.entry = .index definition →
        definition.readsColumn position index = false) ∧
    stored.outline = (database.catalog.dropColumn position index).outline ∧
    stored.selectedParents = (database.catalog.dropColumn position index).selectedParents := by
  obtain ⟨droppable, kept⟩ := Bool.and_eq_true_iff.mp runs
  exact ⟨Catalog.droppable_spec droppable, Catalog.keepsOutline_eq kept⟩

/-- For every database, two facts about tables, position, index and table at the position: if the database has the
first fact in every table, the first fact at another position gives the second, and the first fact at the position gives
the second for the table without the column, the database with the catalog after the drop and the rows without the
cell has the second fact in every table. Proof sketch: {name}`Database.table_dropColumn`. -/
theorem Database.EveryTable.dropColumn {database : Database} {fact fact' : Nat → Table → Prop} {position index : Nat}
    {shape : CatalogTable} (found : database.catalog.tableAt position = some shape) (every : database.EveryTable fact)
    (others : ∀ other table, other ≠ position → fact other table → fact' other table)
    (dropped : ∀ table, database.table position = some table → fact position table →
      fact' position (table.dropColumn index)) :
    (database.dropColumn position index (database.catalog.dropColumn position index)).EveryTable fact' := by
  intro other table present
  rw [Database.table_dropColumn database found other] at present
  by_cases same : position = other
  · subst same
    simp only [↓reduceIte] at present
    obtain ⟨first, hfirst, rfl⟩ := Option.map_eq_some_iff.mp present
    exact dropped first hfirst (every position first hfirst)
  · simp only [same, ↓reduceIte] at present
    exact others other table (Ne.symm same) (every other table present)

end Belay.Sqlite.Model
