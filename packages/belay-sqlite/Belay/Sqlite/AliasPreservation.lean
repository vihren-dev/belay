import Belay.Sqlite.LiteralPreservation
import Belay.Sqlite.RowUpdate

set_option doc.verso true

/-! Row lemmas for rowid aliases (ADR 0012, amendment 4, slice 5b): the cells that INSERT
writes for a new row keep their width and stored form and make the row
{lit}`Row.Aliased`, and the rows that INSERT appends keep {lit}`Table.RowsValid`. The
distinct rowids of a write's result come from the check of {lit}`checkedWrite`, not
from the rows themselves, since an explicit alias may repeat a rowid. UPDATE is in
{lit}`UpdatePreservation`. -/

namespace Belay.Sqlite

/-- For every table, cell list and rowid, {name}`LiteralData.newCells` keeps the number
of cells. Proof sketch: with an alias it sets one cell, which keeps the length; without
one it keeps the cells. -/
theorem LiteralData.newCells_length (table : Table) (values : List Value) (rowid : Int) :
    (newCells table values rowid).length = values.length := by
  unfold newCells
  split <;> simp

/-- For every table, cell list and rowid: if the cells are {name}`Row.Stored` for the
table's columns and the alias is {name}`LiteralData.aliasReady`, the cells of
{name}`LiteralData.newCells` are stored too. Proof sketch: the alias cell becomes an
integer, which INTEGER affinity keeps; every other cell stays. -/
theorem Row.Stored.newCells {table : Table} {values : List Value} {rowid other : Int}
    (stored : Row.Stored table.shape.columns { rowid := other, values })
    (ready : LiteralData.aliasReady table.shape = true) :
    Row.Stored table.shape.columns { rowid, values := LiteralData.newCells table values rowid } := by
  intro index column cell columnAt cellAt
  unfold LiteralData.newCells at cellAt
  split at cellAt
  · rename_i position alias
    by_cases same : index = position
    · subst same
      have integer : column.affinity = .integer := by
        simp only [LiteralData.aliasReady, alias, Option.all_some, Option.any_eq_true, beq_iff_eq] at ready
        obtain ⟨found, foundAt, affinity⟩ := ready
        rw [columnAt] at foundAt
        cases foundAt
        exact affinity
      have value : cell = .integer rowid := by
        rw [List.getElem?_set_self'] at cellAt
        cases h : values[index]? with
        | none => simp [h] at cellAt
        | some _ => simp [h] at cellAt; exact cellAt.symm
      subst value
      rw [integer]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm same)] at cellAt
      exact stored index column cell columnAt cellAt
  · exact stored index column cell columnAt cellAt

/-- For every table, cell list and rowid: if the cells have one value per column and the
alias is {name}`LiteralData.aliasReady`, the row of the rowid and
{name}`LiteralData.newCells` is {name}`Row.Aliased`. Proof sketch: the alias position is
a column, so a cell, and {name}`LiteralData.newCells` sets it to the rowid. -/
theorem Row.Aliased.newCells {table : Table} {values : List Value} {rowid : Int}
    (width : values.length = table.shape.columns.length) (ready : LiteralData.aliasReady table.shape = true) :
    Row.Aliased table.shape.rowidAlias { rowid, values := LiteralData.newCells table values rowid } := by
  intro position alias
  simp only [LiteralData.aliasReady, alias, Option.all_some, Option.any_eq_true] at ready
  obtain ⟨_, foundAt, _⟩ := ready
  have inside : position < values.length := width ▸ (List.getElem?_eq_some_iff.mp foundAt).1
  simp [LiteralData.newCells, alias, inside]

/-- For every table and cell list: assume {name}`Table.RowsValid`,
{name}`LiteralData.aliasReady`, a valid new rowid, one value per column and the cells in
stored form. Then {name}`LiteralData.insertRow` keeps {name}`Table.RowsValid`. Proof
sketch: the old rows keep their conditions; the new row has the bounded rowid, the width
by {name}`LiteralData.newCells_length`, the stored form by {name}`Row.Stored.newCells`,
and the alias by {name}`Row.Aliased.newCells`. -/
theorem Table.RowsValid.insertRow {table : Table} {values : List Value} (valid : table.RowsValid)
    (ready : LiteralData.aliasReady table.shape = true) (bounded : validRowid (LiteralData.newRowid table values))
    (width : values.length = table.shape.columns.length)
    (stored : Row.Stored table.shape.columns { rowid := 0, values }) :
    (LiteralData.insertRow table values).RowsValid := by
  intro row member
  simp only [LiteralData.insertRow, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact valid row old
  · exact ⟨bounded, (LiteralData.newCells_length ..).trans width, stored.newCells ready,
      Row.Aliased.newCells width ready⟩

end Belay.Sqlite
