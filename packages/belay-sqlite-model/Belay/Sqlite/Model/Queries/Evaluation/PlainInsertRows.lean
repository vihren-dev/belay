import Belay.Sqlite.Model.Queries.Evaluation.SelectCalmRule
import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws
import Belay.Sqlite.Model.Values.Scalar.LiteralData
import Belay.Sqlite.Model.Queries.Evaluation.CountOf
import Belay.Sqlite.Model.Queries.Evaluation.Subqueries
import Belay.Sqlite.Model.Queries.Evaluation.ComparisonLaws
import Belay.Sqlite.Model.Queries.Preparation.CatalogSpec

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every table, the rows of a scan ({lit}`Resolved.sourceRows`) are a permutation of the
cells of its rows. Proof sketch: a scan is a permutation of the rows ({lit}`Table.scanRows_perm`). -/
theorem sourceRows_perm (table : Table) : (Resolved.sourceRows table).Perm (table.rows.map Row.values) := by
  unfold Resolved.sourceRows
  exact table.scanRows_perm.map _

/-- For every table and list of cells, the cells are a scanned row exactly when some stored row has
them. Proof sketch: {name}`sourceRows_perm` keeps membership. -/
theorem mem_sourceRows_iff (table : Table) (values : List Value) :
    values ∈ Resolved.sourceRows table ↔ ∃ row ∈ table.rows, row.values = values := by
  rw [(sourceRows_perm table).mem_iff]
  simp

/-- For every context, condition, table and row: if the condition is true for no scanned row of
the table and true for the cells of the new row, then it is true for exactly one scanned row of
the table with the new row appended ({lit}`Resolved.countMatching`). Proof sketch: the scan of the
longer table is a permutation of the old cells and the new cells; the filter of the old cells is
empty and the filter of the new cell list keeps it. -/
theorem countMatching_appended (context : Resolved.EvalContext) (condition : Option Resolved.Expr)
    (table : Table) (row : Row)
    (unmatched : ∀ values ∈ Resolved.sourceRows table,
      condition.all (fun expression => Resolved.truthy (expression.eval context values)) = false)
    (appendedMatches : condition.all (fun expression => Resolved.truthy (expression.eval context row.values)) = true) :
    Resolved.countMatching context condition { table with rows := table.rows ++ [row] } = 1 := by
  unfold Resolved.countMatching
  have perm := (sourceRows_perm { table with rows := table.rows ++ [row] }).filter
    (fun values => condition.all fun expression => Resolved.truthy (expression.eval context values))
  rw [perm.length_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, List.filter_append]
  have empty : (table.rows.map Row.values).filter
      (fun values => condition.all fun expression => Resolved.truthy (expression.eval context values)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro values mem
    have := unmatched values ((mem_sourceRows_iff table values).2 (by simpa using mem))
    simp [this]
  rw [empty]
  simp [appendedMatches]

/-- The resolved condition {lit}`c = ?n` of a column: the column at a position compared with
parameter {lit}`n` under the affinity and the collation of the column. -/
def equalsParameter (cell : CatalogColumn) (position index : Nat) : Resolved.Expr :=
  .compare .eq (some cell.affinity) (.column position) (.parameter index) cell.collation

/-- For every column, position, parameter number, parameters and row: the condition
{name}`equalsParameter` is true when the cell of the row and the bound parameter are one value
that is not NULL, and the affinity leaves the value as it is. Proof sketch: unfold the comparison;
equal values are equal under every collation ({lit}`Collation.compare_eq_of_binary`). -/
theorem equalsParameter_true (cell : CatalogColumn) (position index : Nat) (parameters row : List Value)
    (stored : Value) (cellIs : row[position]?.getD .null = stored)
    (bound : boundValue (parameters[index - 1]?.getD .null) = stored) (notNull : stored.isNull = false)
    (same : Resolved.comparisonOperands (some cell.affinity) stored stored = (stored, stored)) :
    Resolved.truthy ((equalsParameter cell position index).eval (Resolved.EvalContext.bound parameters) row) =
      true := by
  simp [equalsParameter, Resolved.Expr.eval_compare, Resolved.Expr.eval_column,
    Resolved.Expr.eval_parameter, parameterValue, cellIs, bound, same]
  simp [Resolved.truthy_apply_ordinary, notNull, Comparison.holds, Collation.compare_eq_of_binary (Std.ReflCmp.compare_self (cmp := Value.compare))]

/-- For every column with INTEGER affinity and every integer, the affinity leaves a comparison of
the integer with itself as it is. Proof sketch: an integer is not text, so it stays a number. -/
theorem comparisonOperands_integer (cell : CatalogColumn) (value : Int) (integer : cell.affinity = .integer) :
    Resolved.comparisonOperands (some cell.affinity) (.integer value) (.integer value) =
      (.integer value, .integer value) := by
  simp [integer, Resolved.comparisonOperands, Resolved.numericOperand]

/-- For every column with TEXT affinity and every text, the affinity leaves a comparison of the text
with itself as it is. Proof sketch: a text stays text under TEXT affinity. -/
theorem comparisonOperands_text (cell : CatalogColumn) (value : List UInt8) (text : cell.affinity = .text) :
    Resolved.comparisonOperands (some cell.affinity) (.text value) (.text value) =
      (.text value, .text value) := by
  simp [text, Resolved.comparisonOperands, Value.isText, Value.store]

end Belay.Sqlite.Model
