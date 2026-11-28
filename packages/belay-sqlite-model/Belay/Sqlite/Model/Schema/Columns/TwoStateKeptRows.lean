import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun
import Belay.Sqlite.Model.Queries.Evaluation.RowFilter
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateNotExistsExcept
import Belay.Sqlite.Model.Schema.Writes.PlainInsertRows
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyLookupRemoval
import Belay.Sqlite.Model.Queries.Evaluation.TwoStateKeptRows

set_option doc.verso true

/-! The rows of the two terms of {lit}`SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t` over a table and the
table that a {lit}`DELETE` leaves (ADR 0017, S6). The first term reads the rows of the table before the delete for
which {lit}`p` is true; the second reads every row of the table after it. This file characterizes which rows kept by
the first predicate survive the delete. {name}`Belay.Sqlite.Model.Resolved.project_selected_subset` carries the inclusion
to the projected results of the two terms. If the first column is the rowid
alias, the rows of the first term are identical where they compare equal. -/

namespace Belay.Sqlite.Model

/-- For every table, evaluation context and optional DELETE predicate, scanning the table
produced by {name}`LiteralData.deleted` gives a permutation of the original rows for which
{name}`Resolved.conditionKeeps` is false. A false or NULL predicate keeps that row in the table.
Omitting the predicate deletes every row. Proof sketch: project the row values in
{name}`Table.scan_filterRows` and move the filter through that projection. -/
theorem Resolved.sourceRows_deleted (table : Table) (ctx : Resolved.EvalContext) (p : Option Resolved.Expr) :
    (sourceRows (LiteralData.deleted ctx table p)).Perm
      ((sourceRows table).filter fun row => !(conditionKeeps p ctx row)) := by
  simpa only [sourceRows, List.filter_map, Function.comp_def, conditionKeeps,
    LiteralData.selected, LiteralData.deleted, Table.filterRows] using
    (table.scan_filterRows (fun r => !LiteralData.selected ctx p r)).map Row.values

/-- For every table, keep predicate, context and optional DELETE filter, every value in the
original scan for which the keep predicate is true occurs after the delete exactly when the keep
predicate and the DELETE filter are disjoint on that scan ({name}`RowFilter.DisjointOn`).
With no DELETE filter, this requires the keep predicate to be false for all rows in the scan.
Proof sketch: {name}`Resolved.sourceRows_deleted`
turns membership after the delete into membership in the filtered scan. -/
theorem Resolved.selected_subset_deleted_iff {table : Table} {ctx : Resolved.EvalContext}
    {filter : Option Resolved.Expr} {keep : List Value → Bool} :
    (sourceRows table).filter keep ⊆ sourceRows (LiteralData.deleted ctx table filter) ↔
      RowFilter.DisjointOn (sourceRows table) keep (conditionKeeps filter ctx) := by
  rw [RowFilter.disjointOn_iff_impliesOn_complement, RowFilter.impliesOn_iff_subset]
  exact forall_congr' fun _ => imp_congr_right fun _ => (sourceRows_deleted table ctx filter).mem_iff

/-- For every table with distinct rowids whose rowid alias is the first column, every context, condition, and columns
and collations that both start with the first column: no two results of the first term over the table compare equal
unless they are the same list. In plain words: equal keys mean the same row. Proof sketch: the first cell of a row
is its rowid ({name}`Row.Aliased`), so two results that compare equal in the first cell come from rows with
the same rowid, which are one row ({name}`Table.RowidsDistinct.row_eq`). -/
theorem Resolved.notExistsExcept_identical (position : Nat) (condition : Resolved.Expr) (first : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (collation : Collation) (collations : List Collation)
    (table : Table) (context : Resolved.EvalContext) (distinct : table.RowidsDistinct) (aliased : table.RowsAliased)
    (alias : table.shape.rowidAlias = some 0) (firstColumn : first = .column 0) :
    Resolved.equalRowsIdentical (collation :: collations)
      ((Resolved.initialTerm position condition (first :: columns) names).results context (Resolved.sourceRows table)) =
      true := by
  unfold Resolved.equalRowsIdentical
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  intro left leftMember right rightMember
  by_cases same : Resolved.sameOutput (collation :: collations) left right = true
  · right
    obtain ⟨leftCells, leftScanned, -, rfl⟩ := (Resolved.initialTerm_mem_results _ _ _ _ _ _ _).1 leftMember
    obtain ⟨rightCells, rightScanned, -, rfl⟩ := (Resolved.initialTerm_mem_results _ _ _ _ _ _ _).1 rightMember
    obtain ⟨leftRow, leftIn, rfl⟩ := (mem_sourceRows_iff table leftCells).1 leftScanned
    obtain ⟨rightRow, rightIn, rfl⟩ := (mem_sourceRows_iff table rightCells).1 rightScanned
    have leftKey := aliased leftRow leftIn 0 alias
    have rightKey := aliased rightRow rightIn 0 alias
    have compared : collation.compare (leftRow.values.getD 0 .null) (rightRow.values.getD 0 .null) = .eq := by
      unfold Resolved.sameOutput at same
      simp only [Bool.and_eq_true, List.all_eq_true] at same
      have head := same.2 (collation, leftRow.values.getD 0 .null, rightRow.values.getD 0 .null) (by
        simp [firstColumn, Resolved.Expr.eval, Resolved.Expr.evaluate])
      simpa using head
    simp only [List.getD_eq_getElem?_getD, leftKey, rightKey, Option.getD_some,
      Collation.compare_integer, Int.compare_eq_eq] at compared
    have sameRow : leftRow = rightRow := distinct.row_eq leftIn rightIn compared
    rw [sameRow]
  · left
    simpa using same

end Belay.Sqlite.Model
