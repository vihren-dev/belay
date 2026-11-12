import Belay.Sqlite.Model.Schema.Dispatch.InSubqueryColumnLaw

set_option doc.verso true

/-! The structural premises of the filter laws of {lit}`x NOT IN (SELECT c FROM u)` and {lit}`x IN (SELECT c FROM u)` (task 20261027). When {lit}`x` is a
rowid alias of the outer table, the key cell of every outer row is an integer, and for an integer probe the
{lit}`IN` test and the correlated comparison match the same candidates, whatever type, affinity and collation the
candidates have ({name}`Belay.Sqlite.Model.Resolved.inMatches_integer_collation_free`). So the premises that the filter law needs
for the key are checkable facts about the outer table; the remaining premise is that no cell of the column {lit}`c`
is NULL. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every table with a rowid alias at a position, whose rows all have their alias cell equal to their rowid
({name}`Table.RowsAliased`), and every row of the table as a source row ({name}`sourceRows`): the cell at the position
is an integer. Proof sketch: the source row is the values of a row of the table (the scan order permutes the rows,
{name}`Table.scanRows_perm`), and the alias cell of that row is its rowid. -/
theorem sourceRows_alias_cell (table : Table) (position : Nat) (alias : table.shape.rowidAlias = some position)
    (aliased : table.RowsAliased) (row : List Value) (member : row ∈ sourceRows table) :
    ∃ number : Int, row.getD position .null = .integer number := by
  obtain ⟨found, inScan, rfl⟩ := List.mem_map.mp member
  have inRows := table.scanRows_perm.subset inScan
  have cell := aliased found inRows position alias
  exact ⟨found.rowid, by simp [List.getD_eq_getElem?_getD, cell]⟩

end Belay.Sqlite.Model.Resolved
