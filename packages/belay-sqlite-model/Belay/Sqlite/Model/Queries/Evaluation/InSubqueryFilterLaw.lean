import Belay.Sqlite.Model.Queries.Evaluation.InSubqueryEvaluate

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- The condition of the correlated {lit}`EXISTS` subquery keeps a joined row exactly when the {lit}`IN` subquery
keeps it and its result expression is equal to the probe value under the affinity and the collation of the comparison
{lit}`=` (with the result expression as the left operand, as in {lit}`u.c = x`). Formally: for every row in the list,
{name}`conditionKeeps` of the correlated condition is the conjunction of {name}`conditionKeeps` of the {lit}`IN`
condition and the truth of {name}`equalsValue` of the result expression and the value. -/
def CorrelatedEquality (inner : EvalContext) (affinity : Option Affinity) (collation : Collation)
    (conditionIn conditionExists : Option Expr) (projection : Expr) (value : Value) (rows : List (List Value)) : Prop :=
  ∀ row ∈ rows, conditionKeeps conditionExists inner row =
    (conditionKeeps conditionIn inner row && truthy (equalsValue affinity collation (projection.eval inner row) value))

/-- For every list, tests and function, some element of the mapped kept list passes the second test exactly when some
element passes both tests after the function. Proof sketch: induction on the list. -/
theorem any_filter_map {α β : Type} (elements : List α) (keep : α → Bool) (change : α → β) (test : β → Bool) :
    ((elements.filter keep).map change).any test = elements.any (fun element => keep element && test (change element)) := by
  induction elements with
  | nil => rfl
  | cons element rest ih =>
    cases hkeep : keep element <;> simp [hkeep, ih]

/-- The kept joined rows have a true equality exactly when the correlated condition keeps a joined row. Proof
sketch: {name}`any_congr_of_mem` with the link and {name}`any_filter_map`. -/
theorem any_kept_equals_iff (inner : EvalContext) (affinity : Option Affinity) (collation : Collation)
    (conditionIn conditionExists : Option Expr) (projection : Expr) (value : Value) (rows : List (List Value))
    (link : CorrelatedEquality inner affinity collation conditionIn conditionExists projection value rows) :
    rows.any (conditionKeeps conditionExists inner) =
      ((rows.filter (conditionKeeps conditionIn inner)).map (fun row => projection.eval inner row)).any
        (fun candidate => truthy (equalsValue affinity collation candidate value)) := by
  rw [any_filter_map]
  exact any_congr_of_mem link

end Belay.Sqlite.Model.Resolved
