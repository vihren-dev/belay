import Belay.Sqlite.Model.DatabaseDropColumn
import Belay.Sqlite.Model.DatabaseConstraints
import Belay.Sqlite.Model.Resolution.ColumnDropSpec

set_option doc.verso true

/-! The rows of a table that lost a column (ADR 0019, D4): the facts about the stored rows that hold again
after ALTER TABLE DROP COLUMN. A cell at a position of the shorter row is the cell at the position of the
longer row that {lit}`dropSource` names, and a column at a position of the shorter table is the column at
that position, changed in its constraints only. -/

namespace Belay.Sqlite.Model

/-- The position of the longer list that a position of the list without the item at the index names: a
position before the index is the same, and a position from the index on is one higher. -/
def dropSource (index position : Nat) : Nat := if position < index then position else position + 1

/-- For every index and position other than it: {name}`dropSource` undoes {lit}`dropPosition`. Proof sketch: a
case split on the position against the index. -/
theorem dropSource_dropPosition {index position : Nat} (other : position ≠ index) :
    dropSource index (dropPosition index position) = position := by
  by_cases before : position < index
  · simp [dropSource, dropPosition, before]
  · have after : ¬(position - 1 < index) := by omega
    simp only [dropSource, dropPosition, before, after, ↓reduceIte]
    omega

/-- For every list, index and position: the item at the position of the list without the item at the index is
the item at {name}`dropSource` of the list. Proof sketch: {lit}`List.getElem?_eraseIdx`. -/
theorem getElem?_eraseIdx_source {α : Type} (items : List α) (index position : Nat) :
    (items.eraseIdx index)[position]? = items[dropSource index position]? := by
  by_cases before : position < index <;> simp [dropSource, before, List.getElem?_eraseIdx]

/-- The table after DROP COLUMN: the shape without the column ({name}`CatalogTable.dropColumnAt`) and each row
without the cell of the column ({name}`Row.dropValue`). -/
def Table.dropColumn (index : Nat) (table : Table) : Table :=
  { shape := table.shape.dropColumnAt index, rows := table.rows.map (Row.dropValue index) }

/-- For every table, index and position: the column at the position of the table after the drop is the column at
{name}`dropSource`, changed by the drop. Proof sketch: {name}`getElem?_eraseIdx_source`. -/
theorem Table.dropColumn_column (table : Table) (index position : Nat) :
    (table.dropColumn index).shape.columns[position]? =
      (table.shape.columns[dropSource index position]?).map (·.dropColumn index) := by
  simp [Table.dropColumn, CatalogTable.dropColumnAt, List.getElem?_map, getElem?_eraseIdx_source]

/-- For every row, index and position: the cell at the position of the row without the cell at the index is the
cell at {name}`dropSource`. Proof sketch: {name}`getElem?_eraseIdx_source`. -/
theorem Row.dropValue_cell (row : Row) (index position : Nat) :
    (row.dropValue index).values[position]? = row.values[dropSource index position]? :=
  getElem?_eraseIdx_source row.values index position

/-- For every table, index and its rows: the rowids of the table after the drop are those before it, so a table
without two rows of one rowid keeps that. Proof sketch: the drop keeps the rowid of each row. -/
theorem Table.RowidsDistinct.dropColumn {table : Table} (distinct : table.RowidsDistinct) (index : Nat) :
    (table.dropColumn index).RowidsDistinct := by
  have same : Row.rowid ∘ Row.dropValue index = Row.rowid := rfl
  simpa [Table.RowidsDistinct, Table.dropColumn, List.map_map, same] using distinct

/-- For every table with rowids in the range and every index: the table after the drop has them. Proof sketch:
the drop keeps the rowid of each row. -/
theorem Table.RowidsInRange.dropColumn {table : Table} (inRange : table.RowidsInRange) (index : Nat) :
    (table.dropColumn index).RowidsInRange := by
  intro row member
  obtain ⟨original, inRows, same⟩ := List.mem_map.mp member
  subst same
  exact inRange original inRows

/-- For every table with {name}`Table.RowsWide` and an index inside its columns: the table after the drop has it.
Proof sketch: a row and the columns each lose one place ({lit}`List.length_eraseIdx_of_lt`). -/
theorem Table.RowsWide.dropColumn {table : Table} (wide : table.RowsWide) {index : Nat}
    (inside : index < table.shape.columns.length) : (table.dropColumn index).RowsWide := by
  intro row member
  obtain ⟨original, inRows, same⟩ := List.mem_map.mp member
  subst same
  have := wide original inRows
  simp [Table.dropColumn, Row.dropValue, CatalogTable.dropColumnAt, List.length_eraseIdx_of_lt (this ▸ inside),
    List.length_eraseIdx_of_lt inside, this]

end Belay.Sqlite.Model
