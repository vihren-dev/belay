import Belay.Sqlite.Model.ExprAppendLaws
import Belay.Sqlite.Model.Resolution.ColumnDropExpr

set_option doc.verso true

/-! The value of an expression that does not read a column does not change when the column is dropped from
the row and every position after it moves down ({lit}`Expr.dropColumn`). DROP COLUMN removes one cell
from each row, and the CHECK constraints, the generated expressions, the key terms and the filter of an
index that survive the drop are evaluated over the shorter row (ADR 0019, D4). -/

namespace Belay.Sqlite.Model.Resolved

/-- For every position of a cell and every index, a position after the index finds, in the row without
the cell at the index, the cell that it found in the row. Proof sketch: {lit}`List.getElem?_eraseIdx`
and a case split on the position against the index. -/
theorem dropPosition_getD (index position : Nat) (row : List Value) (other : position ≠ index) :
    ((row.eraseIdx index)[dropPosition index position]?).getD .null = (row[position]?).getD .null := by
  by_cases before : position < index
  · simp [dropPosition, before, List.getElem?_eraseIdx]
  · have after : index < position := by omega
    have : position - 1 ≥ index := by omega
    simp [dropPosition, before, List.getElem?_eraseIdx]
    simp only [show ¬(position - 1 < index) by omega, ↓reduceIte, Nat.sub_add_cancel (show 1 ≤ position by omega)]

/-- For every context whose subqueries do not depend on the outer row ({lit}`EvalContext.RowFree`), index,
row and expression that does not read the column at the index ({lit}`Expr.readsColumn`): the expression
with its positions changed ({lit}`Expr.dropColumn`) has the same value and fault ({lit}`Expr.evaluate`),
and the same JSON subtype ({lit}`Expr.givesJson`), over the row without the cell at the index as the
expression has over the row. Proof sketch: induction over the mutual expression and argument types, as in
{lit}`Expr.evaluate_append`; a column reads the cell that {lit}`dropPosition_getD` gives, a subquery form
reads the same results for both rows, and every other node combines the values of its parts, which are
equal by induction. -/
theorem Expr.evaluate_dropColumn (context : EvalContext) (rowFree : context.RowFree) (index : Nat)
    (row : List Value) (expression : Expr) (free : expression.readsColumn index = false) :
    (expression.dropColumn index).evaluate context (row.eraseIdx index) = expression.evaluate context row ∧
      (expression.dropColumn index).givesJson context (row.eraseIdx index) = expression.givesJson context row := by
  induction expression using Expr.rec
    (motive_2 := fun arguments => arguments.any (Expr.isColumn index) = false →
      (arguments.dropColumn index).evaluate context (row.eraseIdx index) = arguments.evaluate context row ∧
        (arguments.dropColumn index).givesJson context (row.eraseIdx index) = arguments.givesJson context row ∧
        ∀ head tail, arguments = .cons head tail →
          (head.dropColumn index).evaluate context (row.eraseIdx index) = head.evaluate context row ∧
          (tail.dropColumn index).evaluate context (row.eraseIdx index) = tail.evaluate context row)
  case json function arguments ih =>
    have same := ih (by simpa [Expr.readsColumn, Expr.any, Expr.isColumn] using free)
    refine ⟨by simp only [Expr.dropColumn, Expr.evaluate, same.1, same.2], ?_⟩
    have values := congrArg Prod.fst same.1
    cases function <;> try rfl
    rcases arguments with _ | ⟨json, _ | ⟨path, _ | ⟨_, _⟩⟩⟩ <;> try rfl
    simp only [Arguments.dropColumn, Arguments.evaluate, List.cons.injEq] at values
    simp only [Expr.dropColumn, Arguments.dropColumn, Expr.givesJson, values.1, values.2.1]
  case column position =>
    have other : position ≠ index := by simpa [Expr.readsColumn, Expr.any, Expr.isColumn] using free
    simp [Expr.dropColumn, Expr.evaluate, Expr.givesJson, dropPosition_getD index position row other]
  case «exists» number => simp [Expr.dropColumn, Expr.evaluate, Expr.givesJson, rowFree number (row.eraseIdx index) row]
  case subquery number => simp [Expr.dropColumn, Expr.evaluate, Expr.givesJson, rowFree number (row.eraseIdx index) row]
  case inQuery operand number affinity collation negated ih =>
    have same := ih (by simpa [Expr.readsColumn, Expr.any, Expr.isColumn] using free)
    simp [Expr.dropColumn, Expr.evaluate, Expr.givesJson, rowFree number (row.eraseIdx index) row, same.1]
  case scalar function arguments ih =>
    have same := ih (by simpa [Expr.readsColumn, Expr.any, Expr.isColumn] using free)
    cases function
    case iif =>
      rcases arguments with _ | ⟨condition, rest⟩
      · simp [Expr.dropColumn, Arguments.dropColumn, Expr.evaluate, Expr.givesJson]
      · have parts := same.2.2 condition rest rfl
        simp [Expr.dropColumn, Arguments.dropColumn, Expr.evaluate, Expr.givesJson, parts.1, parts.2]
    all_goals simp [Expr.dropColumn, Expr.evaluate, Expr.givesJson, same.1]
  all_goals simp_all [Expr.readsColumn, Expr.any, Arguments.any, Expr.isColumn, Expr.dropColumn, Arguments.dropColumn,
      Expr.evaluate, Arguments.evaluate, Expr.givesJson, Arguments.givesJson]

/-- For every context whose subqueries do not depend on the outer row, index, row and expression that
does not read the column at the index: the expression with its positions changed has the same value
({lit}`Expr.eval`) over the row without the cell at the index as the expression has over the row. Proof
sketch: {lit}`Expr.evaluate_dropColumn`. -/
theorem Expr.eval_dropColumn (context : EvalContext) (rowFree : context.RowFree) (index : Nat)
    (row : List Value) {expression : Expr} (free : expression.readsColumn index = false) :
    (expression.dropColumn index).eval context (row.eraseIdx index) = expression.eval context row := by
  unfold Expr.eval
  rw [(Expr.evaluate_dropColumn context rowFree index row expression free).1]

end Belay.Sqlite.Model.Resolved
