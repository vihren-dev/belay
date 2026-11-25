import Belay.Sqlite.Model.Queries.Evaluation.PlainInsertRows
import Belay.Sqlite.Model.Queries.Evaluation.CompoundRows
import Belay.Sqlite.Model.Queries.Evaluation.IntegerCompareLaws
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyLookupRemoval

set_option doc.verso true

/-! Output rows whose first cell is the rowid of a table row (ADR 0017, S6). The rows of {lit}`q1 EXCEPT q2` are the
first row of each set of rows of {lit}`q1` that compare equal and that equal no row of {lit}`q2`
({name}`Belay.Sqlite.Model.CompoundOperator.combine`). When two rows of {lit}`q1` compare equal but are not identical,
the values of the row that SQLite keeps can depend on its plan. The law here is about one list of output rows over
source rows of a table, with three premises on the table: its rows have distinct rowids
({name}`Belay.Sqlite.Model.Table.RowidsDistinct`), each row stores its rowid in the rowid alias
({name}`Belay.Sqlite.Model.Table.RowsAliased`), and the rowid alias is the column 0 of the table. The first output
column is the column 0 of the source row, and any output columns follow it. Then two output rows that compare equal have
the same rowid, so they come from one row. So the output rows that compare equal are identical
({name}`Belay.Sqlite.Model.Resolved.equalRowsIdentical`). For fixed rows of the first term of {lit}`EXCEPT`, the rows
that the compound keeps then have the same values for each choice of the kept row. The law gives nothing about the order
of the rows. -/

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
