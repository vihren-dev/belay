import Belay.Sqlite.Model.CorrelatedSubqueryRun
import Belay.Sqlite.Model.InValueEqualsAny

set_option doc.verso true

/-! The evaluation of {lit}`probe IN (subquery)` and {lit}`EXISTS (subquery)` for one outer row (task 20261027), when
the context serves the subquery with the run of {name}`Belay.Sqlite.Model.Resolved.Query.oneTable`. The probe is any
expression, the result expression of the subquery is any expression, and the subquery has any optional {lit}`WHERE`
expression. The laws follow {name}`Belay.Sqlite.Model.Resolved.Expr.evaluate`, including the fault join and
{lit}`rowsCertain`. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every list and test, the rows kept by the test, mapped to anything, are empty exactly when no element passes
the test. Proof sketch: a list is empty when no element is kept ({name}`List.filter_eq_nil_iff`). -/
theorem isEmpty_filter_map {α β : Type} (elements : List α) (keep : α → Bool) (change : α → β) :
    ((elements.filter keep).map change).isEmpty = !elements.any keep := by
  rw [List.isEmpty_map]
  cases hany : elements.any keep
  · exact List.isEmpty_iff.mpr (List.filter_eq_nil_iff.mpr (by simpa using List.any_eq_false.mp hany))
  · obtain ⟨element, member, kept⟩ := List.any_eq_true.mp hany
    rw [List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem (List.mem_filter.mpr ⟨member, kept⟩))]
    rfl

/-- For every probe, context that serves subquery 0 with the run of {name}`Query.oneTable` for the outer row, and probe
value: if the probe has the value and no fault for the outer row ({lit}`probeValue`), and no expression of the subquery has a fallible call
({lit}`plain`) or a fault over the empty row or a joined row ({lit}`faultless`), the value of
{lit}`probe IN (SELECT e FROM u WHERE w)` ({name}`Expr.inQuery`, either polarity) is {name}`inValue` of the probe value
and of the values of {lit}`e` over the joined rows that {lit}`w` keeps, and its fault is none. A premise that fails
is not assumed. Proof sketch: the run has these values as its rows, no fault and
certain rows ({name}`Query.oneTable_subqueryRun`), so the fault join of the probe and the run is none. -/
theorem Expr.evaluate_inQuery_oneTable (context inner : EvalContext) (database : Database) (initial : Option Database)
    (position outer : Nat) (condition : Option Expr) (projection probe : Expr) (names : List String) (table : Table)
    (outerRow : List Value) (affinity : Option Affinity) (collation : Collation) (negated : Bool) (value : Value)
    (present : database.table position = some table)
    (plain : ∀ expression ∈ condition.toList ++ [projection], expression.any Expr.isFallibleCall = false)
    (faultless : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ condition.toList ++ [projection], (expression.evaluate inner row).2 = .none)
    (served : context.subqueries 0 outerRow =
      (Query.oneTable position outer condition [projection] names).subqueryRun inner database outerRow initial)
    (probeValue : probe.evaluate context outerRow = (value, .none)) :
    (Expr.inQuery probe 0 affinity collation negated).evaluate context outerRow =
      (inValue affinity collation negated value
        (((joinedRows outer outerRow table).filter (conditionKeeps condition inner)).map
          (fun row => projection.eval inner row)), .none) := by
  obtain ⟨rows, fault, certain⟩ := Query.oneTable_subqueryRun inner database initial position outer condition
    [projection] names table outerRow present plain faultless
  simp only [Expr.evaluate, probeValue, served, rows, fault, certain, Fault.join, ite_true, List.filterMap_map]
  simp [Function.comp_def]

/-- For every context that serves subquery 0 with the run of {name}`Query.oneTable` for the outer row, with any result
expressions, when no expression of the subquery has a fallible call ({lit}`plain`) or a fault over the empty row or a
joined row ({lit}`faultless`), the value of {lit}`EXISTS (SELECT … FROM u WHERE w)` is 1 when some joined row is kept by
{lit}`w`, else 0; its fault is none. Proof sketch: the run has a row for each kept joined row and no fault
({name}`Query.oneTable_subqueryRun`); it has a row exactly when a joined row is kept ({name}`isEmpty_filter_map`). -/
theorem Expr.evaluate_exists_oneTable (context inner : EvalContext) (database : Database) (initial : Option Database)
    (position outer : Nat) (condition : Option Expr) (projections : List Expr) (names : List String) (table : Table)
    (outerRow : List Value) (present : database.table position = some table)
    (plain : ∀ expression ∈ condition.toList ++ projections, expression.any Expr.isFallibleCall = false)
    (faultless : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ condition.toList ++ projections, (expression.evaluate inner row).2 = .none)
    (served : context.subqueries 0 outerRow =
      (Query.oneTable position outer condition projections names).subqueryRun inner database outerRow initial) :
    (Expr.exists 0).evaluate context outerRow =
      (truth ((joinedRows outer outerRow table).any (conditionKeeps condition inner)), .none) := by
  obtain ⟨rows, fault, _⟩ := Query.oneTable_subqueryRun inner database initial position outer condition projections
    names table outerRow present plain faultless
  simp only [Expr.evaluate, served, rows, fault, isEmpty_filter_map, Bool.not_not]

/-- The same for {lit}`NOT EXISTS (SELECT … FROM u WHERE w)`, under the same premises {lit}`plain` and
{lit}`faultless`: the value is 1 when no joined row is kept, else 0; the fault is none. Proof sketch: as for {name}`Expr.evaluate_exists_oneTable`, and NOT of a two-valued test is the other two-valued test. -/
theorem Expr.evaluate_notExists_oneTable (context inner : EvalContext) (database : Database)
    (initial : Option Database) (position outer : Nat) (condition : Option Expr) (projections : List Expr)
    (names : List String) (table : Table) (outerRow : List Value) (present : database.table position = some table)
    (plain : ∀ expression ∈ condition.toList ++ projections, expression.any Expr.isFallibleCall = false)
    (faultless : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ condition.toList ++ projections, (expression.evaluate inner row).2 = .none)
    (served : context.subqueries 0 outerRow =
      (Query.oneTable position outer condition projections names).subqueryRun inner database outerRow initial) :
    (Expr.not (.exists 0)).evaluate context outerRow =
      (truth (!(joinedRows outer outerRow table).any (conditionKeeps condition inner)), .none) := by
  obtain ⟨rows, fault, _⟩ := Query.oneTable_subqueryRun inner database initial position outer condition projections
    names table outerRow present plain faultless
  simp only [Expr.evaluate, served, rows, fault, isEmpty_filter_map, Bool.not_not]
  cases (joinedRows outer outerRow table).any (conditionKeeps condition inner) <;> rfl

end Belay.Sqlite.Model.Resolved
