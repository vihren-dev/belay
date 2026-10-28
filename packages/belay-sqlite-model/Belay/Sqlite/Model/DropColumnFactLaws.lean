import Belay.Sqlite.Model.DropColumnCellLaws
import Belay.Sqlite.Model.Resolution.ColumnDropExprLaws

set_option doc.verso true

/-! The facts about the cells of a table that hold again after ALTER TABLE DROP COLUMN (ADR 0019, D4): the
stored form of the cells, the rowid alias, NOT NULL, the STRICT types and the CHECK constraints. Each cell and
each column of the table after the drop is a cell and a column of the table before it
({lit}`Table.dropColumn_column`, {lit}`Row.dropValue_cell`), and a CHECK constraint that stays reads no
dropped cell ({lit}`Resolved.Expr.eval_dropColumn`). -/

namespace Belay.Sqlite.Model

/-- For every table with {name}`Table.RowsStored` and every index: the table after the drop has it. Proof
sketch: a cell and a column of the table after the drop are those of the table before it at the position
{name}`dropSource`; the drop keeps the affinity of a column. -/
theorem Table.RowsStored.dropColumn {table : Table} (stored : table.RowsStored) (index : Nat) :
    (table.dropColumn index).RowsStored := by
  intro row member position column value found cell
  obtain ⟨original, inRows, same⟩ := List.mem_map.mp member
  subst same
  rw [Table.dropColumn_column] at found
  rw [Row.dropValue_cell] at cell
  obtain ⟨before, foundBefore, rfl⟩ := Option.map_eq_some_iff.mp found
  exact stored original inRows _ before value foundBefore cell

/-- For every table with {name}`Table.RowsAliased` and an index that is not the rowid alias: the table after the
drop has it. Proof sketch: the alias moves with {lit}`dropPosition`, and the cell at the moved position is the cell
at the alias ({name}`Row.dropValue_cell`). -/
theorem Table.RowsAliased.dropColumn {table : Table} (aliased : table.RowsAliased) {index : Nat}
    (notAlias : table.shape.rowidAlias ≠ some index) : (table.dropColumn index).RowsAliased := by
  intro row member position same
  obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
  obtain ⟨alias, isAlias, rfl⟩ := Option.map_eq_some_iff.mp (show (table.shape.rowidAlias.map (dropPosition index)) = some position from same)
  have different : alias ≠ index := fun h => notAlias (h ▸ isAlias)
  rw [Row.dropValue_cell]
  have : dropSource index (dropPosition index alias) = alias := dropSource_dropPosition different
  rw [this]
  exact aliased original inRows alias isAlias

/-- For every table with {name}`Table.NotNull` and every index: the table after the drop has it. Proof sketch: a
cell and a column of the table after the drop are those of the table before it at {name}`dropSource`; the drop
keeps the NOT NULL flag of a column. -/
theorem Table.NotNull.dropColumn {table : Table} (notNull : table.NotNull) (index : Nat) :
    (table.dropColumn index).NotNull := by
  intro row member position column value found cell flagged
  obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
  rw [Table.dropColumn_column] at found
  rw [Row.dropValue_cell] at cell
  obtain ⟨before, foundBefore, rfl⟩ := Option.map_eq_some_iff.mp found
  exact notNull original inRows _ before value foundBefore cell flagged

/-- For every table with {name}`Table.TypesFit` and every index: the table after the drop has it. Proof sketch: as
{name}`Table.NotNull.dropColumn`; the drop keeps the STRICT type of a column. -/
theorem Table.TypesFit.dropColumn {table : Table} (fits : table.TypesFit) (index : Nat) :
    (table.dropColumn index).TypesFit := by
  intro row member position column value found cell
  obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
  rw [Table.dropColumn_column] at found
  rw [Row.dropValue_cell] at cell
  obtain ⟨before, foundBefore, rfl⟩ := Option.map_eq_some_iff.mp found
  exact fits original inRows _ before value foundBefore cell

/-- For every table: the CHECK constraints of the table after the drop are those that stay
({name}`CatalogTable.checksAfterDrop`), changed by the drop. Proof sketch: the columns without the dropped column,
changed, give the changed CHECK constraints of their columns in order. -/
theorem CatalogTable.allChecks_dropColumnAt (table : CatalogTable) (index : Nat) :
    (table.dropColumnAt index).allChecks = (table.checksAfterDrop index).map (CheckConstraint.dropColumn index) := by
  simp [CatalogTable.allChecks, CatalogTable.dropColumnAt, CatalogTable.checksAfterDrop, List.flatMap_map,
    CatalogColumn.dropColumn, List.map_append, List.map_flatMap]

/-- For every table: a CHECK constraint that stays when the column at the index is dropped is a CHECK
constraint of the table. Proof sketch: the column of the constraint is a column of the table
({lit}`List.mem_of_mem_eraseIdx`). -/
theorem CatalogTable.mem_allChecks_of_checksAfterDrop {table : CatalogTable} {index : Nat} {check : CheckConstraint}
    (stays : check ∈ table.checksAfterDrop index) : check ∈ table.allChecks := by
  unfold CatalogTable.checksAfterDrop CatalogTable.allChecks at *
  rcases List.mem_append.mp stays with inColumns | inTable
  · obtain ⟨column, inColumn, inChecks⟩ := List.mem_flatMap.mp inColumns
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨column, List.mem_of_mem_eraseIdx inColumn, inChecks⟩)
  · exact List.mem_append_right _ inTable

/-- For every row, index and CHECK constraint that does not read the column at the index: the constraint after the
drop holds on the row without the cell exactly when the constraint holds on the row. Proof sketch: the two
conditions have one value ({lit}`Resolved.Expr.eval_dropColumn`). -/
theorem LiteralData.checkHolds_dropValue (row : Row) (index : Nat) {check : CheckConstraint}
    (free : check.condition.readsColumn index = false) :
    LiteralData.checkHolds (row.dropValue index) (check.dropColumn index) = LiteralData.checkHolds row check := by
  unfold LiteralData.checkHolds
  simp only [CheckConstraint.dropColumn, Row.dropValue]
  rw [Resolved.Expr.eval_dropColumn _ (Resolved.EvalContext.plain_rowFree 0) index row.values free]

/-- For every table with {name}`Table.ChecksHold` and an index that the table can lose
({name}`CatalogTable.DropsCleanly`): the table after the drop has it. Proof sketch: a CHECK constraint of the table
after the drop is a constraint that stays, changed by the drop ({name}`CatalogTable.allChecks_dropColumnAt`); it reads
no dropped cell, so it holds on the row without the cell as the constraint holds on the row
({name}`LiteralData.checkHolds_dropValue`). -/
theorem Table.ChecksHold.dropColumn {table : Table} (holds : table.ChecksHold) {index : Nat}
    (clean : table.shape.DropsCleanly index) : (table.dropColumn index).ChecksHold := by
  intro row member check inChecks
  obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
  have inChecks : check ∈ (table.shape.checksAfterDrop index).map (CheckConstraint.dropColumn index) := by
    simpa [Table.dropColumn, CatalogTable.allChecks_dropColumnAt] using inChecks
  obtain ⟨stays, inStays, rfl⟩ := List.mem_map.mp inChecks
  rw [LiteralData.checkHolds_dropValue original index (clean.checks stays inStays)]
  exact holds original inRows stays (CatalogTable.mem_allChecks_of_checksAfterDrop inStays)

end Belay.Sqlite.Model
