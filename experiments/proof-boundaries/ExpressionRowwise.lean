import ExpressionAgreement
import Belay.Sqlite.Model.RowwiseExpr

set_option doc.verso true

/-! Experiment: context independence is a read boundary, not a whitelist of operators. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- A conservative test for a node reading something other than its row or parameters.
All date calls are counted; refining their clock dependence is outside this experiment. -/
def readsBeyondRowAndParameters : Expr → Bool
  | .now _ | .date .. | .counter _ | .aggregateValue _ | .exists _ | .subquery _ | .inQuery .. => true
  | _ => false

/-- Any expression whose primitive reads are confined to the row and parameters is
independent of the remaining context, including arithmetic, casts, scalar and JSON calls.
Proof sketch: equal parameters and the same row give every admitted primitive read. -/
theorem evaluate_rowAndParameters (expression : Expr)
    (localReads : expression.any readsBeyondRowAndParameters = false)
    (first second : EvalContext) (row : List Value) (parameters : first.parameters = second.parameters) :
    expression.evaluate first row = expression.evaluate second row ∧
      expression.givesJson first row = expression.givesJson second row := by
  apply evaluate_agrees first second row row readsBeyondRowAndParameters _ expression localReads
  intro node allowed
  cases node <;> simp_all [readsBeyondRowAndParameters, NodeAgrees]

/-- Existing rowwise expressions satisfy the broader read boundary. Proof sketch:
induct on the rowwise certificate, without reasoning about the evaluator. -/
theorem rowwise_local {expression : Expr} (rowwise : expression.Rowwise) :
    expression.any readsBeyondRowAndParameters = false := by
  induction rowwise <;> simp_all [Expr.any, readsBeyondRowAndParameters]

/-- The existing rowwise congruence formula follows by projecting the general result.
The only specialized induction is the small syntax-classification adapter above. -/
theorem evaluate_rowwise {expression : Expr} (rowwise : expression.Rowwise)
    (first second : EvalContext) (row : List Value) (same : first.parameters = second.parameters) :
    expression.evaluate first row = expression.evaluate second row :=
  (evaluate_rowAndParameters expression (rowwise_local rowwise) first second row same).1

#print axioms evaluate_rowAndParameters
#print axioms evaluate_rowwise

end ProofBoundaries
