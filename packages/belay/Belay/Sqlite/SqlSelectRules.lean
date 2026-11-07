import Belay.Sqlite.SqlSelectRule
import Belay.Sqlite.SelectCatalogCheck
import Belay.Sqlite.Model

set_option doc.verso true

/-! The built-in rules and evaluation laws of {lit}`sql_select`. Each registration is global, so every
file that imports the tactic has them. The phase rules turn a membership in the results of a query or in
the scanned rows of a table into facts; the evaluation laws ({lit}`sql_select_simp`) are proved equations
that the simplifier uses on these facts and on the goal. An equation that holds only by definition and
that exposes the evaluation of an expression is stated and proved as a theorem, because a definitional
step there makes the kernel unfold the evaluator, which can exceed its recursion depth. -/

namespace Belay.Sqlite.Select
open Belay.Sqlite.Model

/-- Sublist-lift rule: for every function, list and sublist of the list's images, some sublist of the
list has the sublist as its images. Proof sketch:
{name}`List.sublist_map_iff`. -/
theorem exists_sublist_map_eq {α β : Type} (f : α → β) {images : List β} {items : List α}
    (sublist : images.Sublist (items.map f)) : ∃ chosen : List α, chosen.Sublist items ∧ images = chosen.map f :=
  List.sublist_map_iff.mp sublist

/-- For every list, keeping the items that pass the test that is always true keeps every item. Proof
sketch: {name}`List.filter_eq_self`. -/
theorem filter_const_true {α : Type} (items : List α) : items.filter (fun _ => true) = items :=
  List.filter_eq_self.mpr fun _ _ => rfl

attribute [sql_select_rule execution] Run.query_returnsResult_ofCatalog Sql.check_query_ofCatalog
attribute [sql_select_rule source] Database.mem_scanAt
attribute [sql_select_rule expression] exists_sublist_map_eq Resolved.exists_perm_map_eq
attribute [sql_select_rule aggregate] Resolved.Query.mem_possibleResults_ungrouped
attribute [sql_select_rule project] Resolved.Query.perm_of_mem_possibleResults_plain
  Resolved.Query.mem_possibleResults_plain
attribute [sql_select_rule order] Resolved.Query.exists_sorted_perm_of_mem_possibleResults
attribute [sql_select_rule window] Resolved.Query.exists_sorted_of_mem_possibleResults_window
  Resolved.Query.length_of_mem_possibleResults Resolved.Query.perm_of_mem_possibleResults

/- The results of a query: the kept rows, the records, the groups and the order. -/
attribute [sql_select_simp] Resolved.Query.fails Resolved.filtered filter_const_true Resolved.Query.uniqueRecords
  Resolved.records_plain Resolved.records_aggregate Resolved.filterMap_ite_eq_map_filter Resolved.queryGroups_grouped
  Resolved.Query.keepsGroup_of_having Resolved.Query.groupRecord Resolved.Query.groupContext
  Resolved.Query.groupRow_none Resolved.Query.rowOutput_eq Resolved.compareSort Resolved.compareTerm
  Ordering.then_eq List.pairwise_map List.map_map Function.comp_def NotNullCells

/- The values of expressions and aggregates. -/
attribute [sql_select_simp] Resolved.Expr.eval_column Resolved.Expr.eval_literal Resolved.Expr.eval_parameter
  parameterValue Resolved.Expr.eval_compare Resolved.Expr.eval_aggregateValue Resolved.countRows_eval
  Resolved.Aggregate.fails_countRows

/- Comparison, truth and NULL. -/
attribute [sql_select_simp] Resolved.comparisonOperands_none Resolved.comparisonOperands_isNull
  Resolved.truthy_isNot_null Resolved.truthy_apply_ordinary Comparison.holds Collation.compare_integer
  Int.compare_eq_gt Int.compare_beq_gt Int.ofNat_literal_lt_natCast Value.isNull_integer Value.isNull_real
  Value.isNull_text Value.isNull_blob Value.isNull_iff Value.isNull_eq_false_iff

end Belay.Sqlite.Select
