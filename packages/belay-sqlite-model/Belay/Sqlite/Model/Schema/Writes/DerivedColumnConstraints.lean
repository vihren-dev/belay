import Belay.Sqlite.Model.Schema.Columns.DerivedColumnTable
import Belay.Sqlite.Model.Schema.Columns.Database
import Belay.Sqlite.Model.Schema.Rows.KeysUniqueAddColumn
import Belay.Sqlite.Model.Schema.Rows.DatabaseConstraintChecks

set_option doc.verso true

/-! The declared constraints of a table with a column appended, with any cell in each row
({lit}`Table.appendCells`). The new column has no NOT NULL, no STRICT type and no CHECK, and the old checks
and keys read only old columns, so the cell that each row gets changes no constraint: the table with the
column keeps every constraint that the old table has. ADD COLUMN gives such a table with NULL cells, and
the backfill UPDATE of a derived-column migration gives one with the derived cells
({lit}`Table.addDerivedColumn`), so the write check of the backfill passes. -/

namespace Belay.Sqlite.Model

/-- The table with the column appended to its shape and the cell of the function appended to each row.
Rowids and row order stay. For example, {name}`Table.addDerivedColumn` appends the stored value of an
expression over the row. -/
def Table.appendCells (table : Table) (column : CatalogColumn) (cell : Row → Value) : Table :=
  { shape := { table.shape with columns := table.shape.columns ++ [column] },
    rows := table.rows.map fun row => row.appendValues [cell row] }

/-- For every table with wide rows, column, cell function, row of the table with the cells appended, and
position at which the appended shape has a column and the row has a cell: there is an old row of the table
such that the row is the old row with one value appended, and one of these holds:

* the old shape has the same column at the position, and the old row has the same cell there;
* the column at the position is the appended column.

Proof sketch: split the appended lists at the width. -/
theorem Table.appendCells_cases {table : Table} (wide : table.RowsWide) {column : CatalogColumn}
    {cell : Row → Value} {row : Row} (member : row ∈ (table.appendCells column cell).rows)
    {position : Nat} {atColumn : CatalogColumn} {atValue : Value}
    (hasColumn : (table.appendCells column cell).shape.columns[position]? = some atColumn)
    (hasValue : row.values[position]? = some atValue) :
    ∃ old ∈ table.rows, (∃ extra, row = old.appendValues [extra]) ∧
      ((table.shape.columns[position]? = some atColumn ∧ old.values[position]? = some atValue) ∨
        atColumn = column) := by
  simp only [Table.appendCells, List.mem_map] at member hasColumn
  obtain ⟨old, inOld, rfl⟩ := member
  refine ⟨old, inOld, ⟨_, rfl⟩, ?_⟩
  have width := wide old inOld
  simp only [Row.appendValues] at hasValue
  by_cases below : position < table.shape.columns.length
  · rw [List.getElem?_append_left below] at hasColumn
    rw [List.getElem?_append_left (width ▸ below)] at hasValue
    exact .inl ⟨hasColumn, hasValue⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt below)] at hasColumn
    cases rest : position - table.shape.columns.length with
    | zero => simp_all
    | succ _ => simp_all

/-- For every table, column without NOT NULL, STRICT type and CHECK, cell function and keys: if the rows
of the table are wide, the table satisfies {name}`Table.NotNull`, {name}`Table.TypesFit`,
{name}`Table.ChecksHold` and {name}`Table.KeysUnique` for the keys, each of its CHECK constraints and each
key reads only columns below its width, and its rowids are distinct, then the table with the cells
appended ({name}`Table.appendCells`) passes the write check: {name}`LiteralData.constraints` for the keys
and {name}`LiteralData.rowidsDistinct`. The cell function is arbitrary, so the cell of the new column can
be any value. Proof sketch: an old position has the old column and the old cell
({name}`Table.appendCells_cases`), and the new column requires nothing of its cell; an old CHECK
and an old key ignore the appended cell ({name}`Resolved.Expr.eval_append`,
{name}`LiteralData.keyEqual_append`); the rowids are those of the table. -/
theorem Table.appendCells_checked {table : Table} {column : CatalogColumn} {cell : Row → Value}
    {keys : List UniqueKey} (wide : table.RowsWide) (notNull : table.NotNull) (fits : table.TypesFit)
    (holds : table.ChecksHold) (unique : table.KeysUnique keys) (distinct : table.RowidsDistinct)
    (checksBelow : ∀ check ∈ table.shape.allChecks, check.condition.readsBelow table.shape.columns.length = true)
    (keysBelow : ∀ key ∈ keys, key.readsBelow table.shape.columns.length = true)
    (nullable : column.notNull = false) (loose : column.strictType = none) (unchecked : column.checks = []) :
    LiteralData.constraints keys (table.appendCells column cell) = true ∧
      LiteralData.rowidsDistinct (table.appendCells column cell) = true := by
  refine ⟨(Table.constraints_iff _ _).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro row member position atColumn atValue hasColumn hasValue required
    obtain ⟨old, inOld, -, cases⟩ := Table.appendCells_cases wide member hasColumn hasValue
    rcases cases with ⟨oldColumn, oldCell⟩ | rfl
    · exact notNull old inOld position atColumn atValue oldColumn oldCell required
    · rw [nullable] at required; cases required
  · intro row member position atColumn atValue hasColumn hasValue
    obtain ⟨old, inOld, -, cases⟩ := Table.appendCells_cases wide member hasColumn hasValue
    rcases cases with ⟨oldColumn, oldCell⟩ | rfl
    · exact fits old inOld position atColumn atValue oldColumn oldCell
    · rw [loose]; rfl
  · intro row member check inChecks
    simp only [Table.appendCells, List.mem_map] at member
    obtain ⟨old, inOld, rfl⟩ := member
    have oldCheck : check ∈ table.shape.allChecks := by
      simpa [Table.appendCells, CatalogTable.allChecks, List.flatMap_append, unchecked] using inChecks
    have same := Resolved.Expr.eval_append (.plain 0) (Resolved.EvalContext.plain_rowFree 0) old.values
      [cell old] (Nat.le_of_eq (wide old inOld).symm)
      (checksBelow check oldCheck)
    simpa [LiteralData.checkHolds, Row.appendValues, same] using holds old inOld check oldCheck
  · intro key member
    simp only [Table.appendCells]
    rw [List.pairwise_map]
    refine (unique key member).imp_of_mem fun {first second} atFirst atSecond conflictFree => ?_
    rw [LiteralData.keyEqual_append (Nat.le_of_eq (wide first atFirst).symm) (Nat.le_of_eq (wide second atSecond).symm)
      _ _ (keysBelow key member)]
    exact conflictFree
  · simpa [LiteralData.rowidsDistinct, Table.appendCells, List.map_map, Function.comp_def, Row.appendValues,
      Table.RowidsDistinct] using distinct

end Belay.Sqlite.Model
