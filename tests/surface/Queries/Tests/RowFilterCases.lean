import Belay.Sqlite.Model.Queries.Evaluation.RowFilter
import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun

import Belay.Sqlite.Model.Schema.Columns.TwoStateKeptRows
import Belay.Sqlite.Model.Queries.Evaluation.ComparisonTruthRules

set_option doc.verso true

namespace RowFilterCases
open Belay.Sqlite.Model RowFilter

/-- Every filter relation holds on empty input, even for filters that disagree elsewhere. -/
theorem empty_input (p q : α → Bool) :
    ImpliesOn [] p q ∧ AgreeOn [] p q ∧ EmptyOn [] p ∧ DisjointOn [] p q := by
  simp [ImpliesOn, AgreeOn, EmptyOn, DisjointOn]

/-- For arbitrary Boolean decisions on one row, check the complete truth table of each relation
against its scan law. In particular, reversing implication changes the mixed cases. -/
theorem singleton_decisions (a b : Bool) :
    let p := fun _ : Unit => a
    let q := fun _ : Unit => b
    (ImpliesOn [()] p q ↔ (!a || b) = true) ∧
    (AgreeOn [()] p q ↔ a = b) ∧ (EmptyOn [()] p ↔ a = false) ∧
    (DisjointOn [()] p q ↔ (a && b) = false) := by
  dsimp only
  rw [impliesOn_iff_no_counterexample, agreeOn_iff_filter_eq, disjointOn_iff_impliesOn_complement,
    impliesOn_iff_subset]
  simp only [emptyOn_iff_filter_eq_nil]
  cases a <;> cases b <;> decide

/-- For arbitrary lists and filters, a counterexample in either half of the input defeats
implication, including one that first appears at the end. -/
theorem implication_on_append (xs ys : List α) (p q : α → Bool) :
    ImpliesOn (xs ++ ys) p q ↔ ImpliesOn xs p q ∧ ImpliesOn ys p q := by
  simp only [impliesOn_iff_no_counterexample, emptyOn_iff_filter_eq_nil, List.filter_append,
    List.append_eq_nil_iff]

/-- Agreement on an input permits different decisions outside it. The resulting lists retain
the order and both occurrences of a matching row. -/
theorem repeated_rows :
    let xs := [2, 1, 2, 0]
    let p := fun n : Nat => n != 0
    let q := fun n : Nat => n == 1 || n == 2
    AgreeOn xs p q ∧ xs.filter q = [2, 1, 2] ∧ ¬ ImpliesOn (xs ++ [3]) p q := by
  dsimp only
  rw [agreeOn_iff_filter_eq, impliesOn_iff_no_counterexample, emptyOn_iff_filter_eq_nil]
  decide

/-- For SQL TRUE, FALSE and NULL cells, Boolean rejection includes the NULL row while SQL
NOT rejects it. Check disjointness and a failed implication through the resolved WHERE evaluator. -/
theorem nullable_where :
    let xs : List (List Value) := [[.integer 1], [.null], [.integer 0], [.null]]
    let accepts := Resolved.conditionKeeps (some (.column 0)) (.bound [])
    let sqlNot := Resolved.conditionKeeps (some (.not (.column 0))) (.bound [])
    let spared := fun row => !accepts row
    DisjointOn xs accepts spared ∧ ¬ ImpliesOn xs spared sqlNot ∧
      xs.filter spared = [[.null], [.integer 0], [.null]] := by
  dsimp only
  rw [disjointOn_iff_impliesOn_complement, impliesOn_iff_subset, impliesOn_iff_no_counterexample,
    emptyOn_iff_filter_eq_nil]
  decide

/-- Check {name}`Resolved.truthy_isNot` on a non-NULL operand. For every order, including one
with a NULL customer, {lit}`customer_id IS NOT 7` keeps it exactly when {lit}`customer_id IS 7`
would spare it in a DELETE. -/
theorem survives_delete_customer_seven (ctx : Resolved.EvalContext) (row : List Value) :
    let condition := fun op => some (Resolved.Expr.compare op (some .integer) (.column 1) (.literal (.integer 7)) .binary)
    Resolved.conditionKeeps (condition .isNot) ctx row = !Resolved.conditionKeeps (condition .is) ctx row := by
  exact Resolved.truthy_isNot _ _ _

/-- Check that the two projection laws compose with the DELETE scan law. For every table,
context, DELETE filter, selection and projection, a plain DELETE preserves the selected
bag exactly when the selected and deleted rows are disjoint on the original scan. -/
theorem delete_preserves_projected_bag_iff (table : Table) (ctx : Resolved.EvalContext)
    (filter : Option Resolved.Expr) (keep : List Value → Bool) (project : List Value → α) :
    (((Resolved.sourceRows (LiteralData.deleted ctx table filter)).filter keep).map project).Perm
      (((Resolved.sourceRows table).filter keep).map project) ↔
      RowFilter.DisjointOn (Resolved.sourceRows table) keep (Resolved.conditionKeeps filter ctx) := by
  have rewrite := RowFilter.project_after_restrict (Resolved.sourceRows_deleted table ctx filter) keep project
  rw [rewrite.congr_left _, RowFilter.project_restrict_iff, RowFilter.disjointOn_iff_impliesOn_complement]

#print axioms survives_delete_customer_seven
#print axioms delete_preserves_projected_bag_iff
#print axioms empty_input
#print axioms singleton_decisions
#print axioms implication_on_append
#print axioms repeated_rows
#print axioms nullable_where

end RowFilterCases
