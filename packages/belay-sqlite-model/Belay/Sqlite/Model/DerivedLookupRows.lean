import Belay.Sqlite.Model.ExprAppendLaws
import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.InValueEqualsLaws

set_option doc.verso true

/-! Comparisons of a stored derived column against a probe (ADR 0017, S6). A migration adds a column,
stores in it the value of an expression of the old columns, and moves a lookup from the expression to the
stored column. The laws here are about one row: the comparison on the stored cell is the comparison on the
expression when the two comparisons give the same value for the computed value and the probe. The
laws make no claim about affinity or collation; the premise {lit}`agree` states exactly what must hold: the
comparison under the affinity and collation of the stored column and the comparison under those of the
expression give equal values. It fails for some pairs of expression and column. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context that does not depend on the outer row, row, comparison with the stored column's
affinity and collation, comparison with the expression's affinity and collation, expression, probe that
reads only the old cells, value that the expression has on the row, and affinity of the stored column: if the
comparison of the stored cell with the probe gives the same value as the comparison of the computed value
with the probe, then the comparison {lit}`stored op probe` over the row with the stored cell appended gives the
value of the comparison {lit}`expression op probe` over the row. In plain words, moving a comparison from the
expression to its stored column changes no result, provided the two comparisons give equal values: the
stored cell against the probe under the affinity and collation of the stored column, and the computed value
against the probe under the affinity and collation of the expression. Here the stored cell is the computed
value after the affinity of the column ({name}`Value.store`), and its column position is the width of the
row. Proof sketch: the stored column reads the appended cell, the probe reads the same value over the longer row ({name}`Expr.eval_append`), and
{name}`Expr.eval_compare` turns both sides into the comparison of the premise. -/
theorem Expr.eval_compare_stored_left (context : EvalContext) (rowFree : context.RowFree) (row : List Value)
    (operator : Comparison) (storedAffinity affinity : Option Affinity) (storedCollation collation : Collation)
    (derived probe : Expr) (computed : Value) (cellAffinity : Affinity)
    (computes : derived.eval context row = computed) (probeBelow : probe.readsBelow row.length = true)
    (agree : compareValue operator storedAffinity storedCollation (Value.store cellAffinity computed)
        (probe.eval context row) =
      compareValue operator affinity collation computed (probe.eval context row)) :
    (Expr.compare operator storedAffinity (.column row.length) probe storedCollation).eval context
        (row ++ [Value.store cellAffinity computed]) =
      (Expr.compare operator affinity derived probe collation).eval context row := by
  have cell : (row ++ [Value.store cellAffinity computed]).getD row.length .null =
      Value.store cellAffinity computed := by
    simp [List.getD_eq_getElem?_getD]
  rw [Expr.eval_compare, Expr.eval_compare, Expr.eval_column, Expr.eval_append context rowFree row _
    (Nat.le_refl _) probeBelow, computes, cell]
  exact agree

/-- The same law with the probe on the left: for the same premises with the agreement stated for
{lit}`probe op stored`, the comparison {lit}`probe op stored` over the row with the stored cell appended gives
the value of the comparison {lit}`probe op expression` over the row. In plain words, the side of the
expression in the comparison does not matter. Proof sketch: as {name}`Expr.eval_compare_stored_left`. -/
theorem Expr.eval_compare_stored_right (context : EvalContext) (rowFree : context.RowFree) (row : List Value)
    (operator : Comparison) (storedAffinity affinity : Option Affinity) (storedCollation collation : Collation)
    (derived probe : Expr) (computed : Value) (cellAffinity : Affinity)
    (computes : derived.eval context row = computed) (probeBelow : probe.readsBelow row.length = true)
    (agree : compareValue operator storedAffinity storedCollation (probe.eval context row)
        (Value.store cellAffinity computed) =
      compareValue operator affinity collation (probe.eval context row) computed) :
    (Expr.compare operator storedAffinity probe (.column row.length) storedCollation).eval context
        (row ++ [Value.store cellAffinity computed]) =
      (Expr.compare operator affinity probe derived collation).eval context row := by
  have cell : (row ++ [Value.store cellAffinity computed]).getD row.length .null =
      Value.store cellAffinity computed := by
    simp [List.getD_eq_getElem?_getD]
  rw [Expr.eval_compare, Expr.eval_compare, Expr.eval_column, Expr.eval_append context rowFree row _
    (Nat.le_refl _) probeBelow, computes, cell]
  exact agree

/-- For every two values that TEXT affinity leaves unchanged ({name}`Value.store` with TEXT gives the
value itself), applying TEXT affinity to the operands of a comparison is the same as applying no affinity.
In plain words, a TEXT column does not change the comparison of NULL or text values with each other. Proof
sketch: the TEXT case of {name}`comparisonOperands` applies the store to both operands when one is text, and
the store is the identity on both. -/
theorem comparisonOperands_text_of_stored (left right : Value) (leftStored : Value.store .text left = left)
    (rightStored : Value.store .text right = right) :
    comparisonOperands (some .text) left right = comparisonOperands none left right := by
  simp [comparisonOperands, leftStored, rightStored]

end Belay.Sqlite.Model.Resolved
