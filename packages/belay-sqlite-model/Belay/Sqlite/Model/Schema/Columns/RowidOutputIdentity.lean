import Belay.Sqlite.Model.Queries.Evaluation.PlainInsertRows
import Belay.Sqlite.Model.Queries.Evaluation.CompoundRows
import Belay.Sqlite.Model.Queries.Evaluation.IntegerCompareLaws
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyLookupRemoval

set_option doc.verso true

/-! Output rows whose first cell is the rowid of a table row (ADR 0017, S6). A compound {lit}`SELECT` keeps one row
of each set of rows that compare equal, so its rows can depend on the plan of SQLite. When the first output column
reads the rowid alias of the table, two output rows that compare equal come from rows with the same rowid, which are
one row. Then rows that compare equal are identical ({lit}`Resolved.equalRowsIdentical`), and the rows of the
compound do not depend on the plan. -/

namespace Belay.Sqlite.Model.Resolved

/-- Take a table with distinct rowids ({name}`Table.RowidsDistinct`) whose rows store the rowid in the rowid alias
({name}`Table.RowsAliased`), and let the first column be that alias. Take collations, a context, output columns and
a list of rows, each of which is a source row of the table ({name}`sourceRows`). Then the outputs of the column
{lit}`0` followed by the output columns, over the listed rows, are identical where they compare equal
({name}`equalRowsIdentical`). The list can be any part of the source rows, for example the rows that a filter keeps,
and the output columns can be any expressions. Proof sketch: two outputs that compare equal have equal first cells,
which are the integer rowids of their rows, and two rows of the table with the same rowid are one row
({name}`Table.RowidsDistinct.row_eq`). -/
theorem equalRowsIdentical_rowidFirst {table : Table} (distinct : table.RowidsDistinct)
    (aliased : table.RowsAliased) (alias : table.shape.rowidAlias = some 0) (collation : Collation)
    (collations : List Collation) (context : EvalContext) (columns : List Expr) {rows : List (List Value)}
    (scanned : ∀ cells ∈ rows, cells ∈ sourceRows table) :
    equalRowsIdentical (collation :: collations)
      (rows.map fun cells => (Expr.column 0 :: columns).map (·.eval context cells)) = true := by
  unfold equalRowsIdentical
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.mem_map]
  rintro _ ⟨leftCells, leftMember, rfl⟩ _ ⟨rightCells, rightMember, rfl⟩
  by_cases same : sameOutput (collation :: collations) ((Expr.column 0 :: columns).map (·.eval context leftCells))
      ((Expr.column 0 :: columns).map (·.eval context rightCells)) = true
  · right
    obtain ⟨leftRow, leftIn, rfl⟩ := (mem_sourceRows_iff table leftCells).1 (scanned _ leftMember)
    obtain ⟨rightRow, rightIn, rfl⟩ := (mem_sourceRows_iff table rightCells).1 (scanned _ rightMember)
    have compared : collation.compare (leftRow.values.getD 0 .null) (rightRow.values.getD 0 .null) = .eq := by
      unfold sameOutput at same
      simp only [Bool.and_eq_true, List.all_eq_true] at same
      simpa using same.2 (collation, leftRow.values.getD 0 .null, rightRow.values.getD 0 .null) (by
        simp [Expr.eval, Expr.evaluate])
    simp only [List.getD_eq_getElem?_getD, aliased leftRow leftIn 0 alias, aliased rightRow rightIn 0 alias,
      Option.getD_some, Collation.compare_integer, Int.compare_eq_eq] at compared
    rw [distinct.row_eq leftIn rightIn compared]
  · left
    simpa using same

end Belay.Sqlite.Model.Resolved
