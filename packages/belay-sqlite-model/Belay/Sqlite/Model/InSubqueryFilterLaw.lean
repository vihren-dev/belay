import Belay.Sqlite.Model.InSubqueryEvaluate
import Belay.Sqlite.Model.InIntegerProbe

set_option doc.verso true

/-! The filter laws of {lit}`probe IN (SELECT e FROM u WHERE w)` and {lit}`probe NOT IN (SELECT e FROM u WHERE w)`
against the correlated {lit}`EXISTS` and {lit}`NOT EXISTS (SELECT … FROM u WHERE …)` (task 20261027): for one row of an
outer query, the conditions keep the row equally when the premises of the value law hold for the rows of {lit}`u`. The
probe is any expression, {lit}`e` is any expression over the joined row, and {lit}`w` is any optional {lit}`WHERE`
expression. The correlated condition is tied to the {lit}`IN` test by one semantic premise
({lit}`CorrelatedEquality`), which the module
{lit}`InSubqueryEqualityLink` proves for the usual syntactic forms. -/

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

/-- **Filter law of NOT IN.** For one outer row, a database with the table {lit}`u`, a context that serves subquery 0
with {lit}`SELECT e FROM u WHERE w` ({name}`Query.oneTable`) and a context that serves subquery 0 with a subquery of
the same table with the correlated condition, the value and fault of {lit}`probe NOT IN (SELECT e FROM u WHERE w)` in
the first context are the value and fault of {lit}`NOT EXISTS (SELECT … FROM u WHERE …)` in the second context, and
the fault is none, under these premises:
* the probe has the value {lit}`value` and no fault for the outer row ({lit}`probeValue`), and the value is not NULL
  ({lit}`probeKnown`);
* the result expression {lit}`e` is not NULL in any joined row that {lit}`w` keeps ({lit}`known`);
* for every such row, the {lit}`IN` test and the comparison {lit}`=` match the value of {lit}`e` equally
  ({name}`inMatches`; {lit}`agree`);
* the correlated condition keeps a joined row exactly when {lit}`w` keeps it and {lit}`e` equals the probe value
  ({lit}`link`: {name}`CorrelatedEquality`);
* no expression of either subquery has a fallible call ({lit}`plainIn`, {lit}`plainExists`), or a fault over the
  empty row or a joined row ({lit}`faultlessIn`, {lit}`faultlessExists`).

Both conditions then have the same value, so a {lit}`WHERE` keeps the row for both or for neither. When
{lit}`probeKnown` fails and the subquery keeps a row, {lit}`NOT IN` is NULL and {lit}`NOT EXISTS` is 1; when
{lit}`known` fails and no row matches, {lit}`NOT IN` is NULL and {lit}`NOT EXISTS` is 1; the law says nothing about
those cases, and the premises are not dropped. When {lit}`agree` fails, the values can differ too. Proof sketch: the
two evaluations ({name}`Expr.evaluate_inQuery_oneTable`, {name}`Expr.evaluate_notExists_oneTable`) give
{name}`inValue` and a two-valued test; the value law ({name}`inValue_negated_eq_not_exists`) equates them after
{name}`any_kept_equals_iff` and the comparison commutes ({name}`equalsValue_comm`). -/
theorem Expr.evaluate_notIn_eq_notExists (inContext existsContext inner : EvalContext) (database : Database)
    (initial : Option Database) (position outer : Nat) (conditionIn conditionExists : Option Expr)
    (projection probe : Expr) (projectionsExists : List Expr) (namesIn namesExists : List String) (table : Table)
    (outerRow : List Value) (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation)
    (value : Value) (present : database.table position = some table)
    (plainIn : ∀ expression ∈ conditionIn.toList ++ [projection], expression.any Expr.isFallibleCall = false)
    (faultlessIn : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ conditionIn.toList ++ [projection], (expression.evaluate inner row).2 = .none)
    (plainExists : ∀ expression ∈ conditionExists.toList ++ projectionsExists,
      expression.any Expr.isFallibleCall = false)
    (faultlessExists : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ conditionExists.toList ++ projectionsExists, (expression.evaluate inner row).2 = .none)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer conditionIn [projection] namesIn).subqueryRun inner database outerRow initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer conditionExists projectionsExists namesExists).subqueryRun inner database
        outerRow initial)
    (probeValue : probe.evaluate inContext outerRow = (value, .none)) (probeKnown : value.isNull = false)
    (known : ∀ row ∈ joinedRows outer outerRow table, conditionKeeps conditionIn inner row = true →
      (projection.eval inner row).isNull = false)
    (agree : ∀ row ∈ joinedRows outer outerRow table, conditionKeeps conditionIn inner row = true →
      inMatches inAffinity inCollation value (projection.eval inner row) =
        inMatches equalsAffinity equalsCollation value (projection.eval inner row))
    (link : CorrelatedEquality inner equalsAffinity equalsCollation conditionIn conditionExists projection value
      (joinedRows outer outerRow table)) :
    (Expr.inQuery probe 0 inAffinity inCollation true).evaluate inContext outerRow =
        (Expr.not (.exists 0)).evaluate existsContext outerRow ∧
      ((Expr.inQuery probe 0 inAffinity inCollation true).evaluate inContext outerRow).2 = .none := by
  rw [Expr.evaluate_inQuery_oneTable inContext inner database initial position outer conditionIn projection probe
      namesIn table outerRow inAffinity inCollation true value present plainIn faultlessIn servedIn probeValue,
    Expr.evaluate_notExists_oneTable existsContext inner database initial position outer conditionExists
      projectionsExists namesExists table outerRow present plainExists faultlessExists servedExists,
    any_kept_equals_iff inner equalsAffinity equalsCollation conditionIn conditionExists projection value _ link]
  refine ⟨?_, rfl⟩
  congr 1
  rw [inValue_negated_eq_not_exists inAffinity inCollation equalsAffinity equalsCollation value _ probeKnown
    (fun candidate member => by
      obtain ⟨row, kept, rfl⟩ := List.mem_map.mp member
      obtain ⟨inRows, keeps⟩ := List.mem_filter.mp kept
      exact known row inRows keeps)
    (fun candidate member => by
      obtain ⟨row, kept, rfl⟩ := List.mem_map.mp member
      obtain ⟨inRows, keeps⟩ := List.mem_filter.mp kept
      exact agree row inRows keeps)]
  simp only [equalsValue_comm equalsAffinity equalsCollation value]

/-- **Filter law of IN.** For the same premises as {name}`Expr.evaluate_notIn_eq_notExists` except that the probe may
be NULL, that {lit}`e` may be NULL, and that the polarity is {lit}`IN` against {lit}`EXISTS`, the condition
{lit}`probe IN (SELECT e FROM u WHERE w)` and the condition {lit}`EXISTS (SELECT … FROM u WHERE …)` have the same
truth and no fault, so a {lit}`WHERE` keeps the row for both or for neither. The values can differ: {lit}`IN` is NULL
where {lit}`EXISTS` is 0, for a NULL probe or a NULL value of {lit}`e` without a match. The premises are
{lit}`probeValue`, {lit}`agree` (only for a probe that is not NULL), {lit}`link` and the fault premises; the law needs
no premise on NULL. Proof sketch:
{name}`truthy_inValue_eq_any` equates the truth of {name}`inValue` with the disjunction of the true comparisons, which
is the truth of the two-valued test of {name}`Expr.evaluate_exists_oneTable` after {name}`any_kept_equals_iff`. -/
theorem Expr.evaluate_in_truthy_eq_exists (inContext existsContext inner : EvalContext) (database : Database)
    (initial : Option Database) (position outer : Nat) (conditionIn conditionExists : Option Expr)
    (projection probe : Expr) (projectionsExists : List Expr) (namesIn namesExists : List String) (table : Table)
    (outerRow : List Value) (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation)
    (value : Value) (present : database.table position = some table)
    (plainIn : ∀ expression ∈ conditionIn.toList ++ [projection], expression.any Expr.isFallibleCall = false)
    (faultlessIn : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ conditionIn.toList ++ [projection], (expression.evaluate inner row).2 = .none)
    (plainExists : ∀ expression ∈ conditionExists.toList ++ projectionsExists,
      expression.any Expr.isFallibleCall = false)
    (faultlessExists : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ conditionExists.toList ++ projectionsExists, (expression.evaluate inner row).2 = .none)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer conditionIn [projection] namesIn).subqueryRun inner database outerRow initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer conditionExists projectionsExists namesExists).subqueryRun inner database
        outerRow initial)
    (probeValue : probe.evaluate inContext outerRow = (value, .none))
    (agree : value.isNull = false → ∀ row ∈ joinedRows outer outerRow table,
      conditionKeeps conditionIn inner row = true →
      inMatches inAffinity inCollation value (projection.eval inner row) =
        inMatches equalsAffinity equalsCollation value (projection.eval inner row))
    (link : CorrelatedEquality inner equalsAffinity equalsCollation conditionIn conditionExists projection value
      (joinedRows outer outerRow table)) :
    truthy ((Expr.inQuery probe 0 inAffinity inCollation false).evaluate inContext outerRow).1 =
        truthy ((Expr.exists 0).evaluate existsContext outerRow).1 ∧
      ((Expr.inQuery probe 0 inAffinity inCollation false).evaluate inContext outerRow).2 = .none ∧
      ((Expr.exists 0).evaluate existsContext outerRow).2 = .none := by
  rw [Expr.evaluate_inQuery_oneTable inContext inner database initial position outer conditionIn projection probe
      namesIn table outerRow inAffinity inCollation false value present plainIn faultlessIn servedIn probeValue,
    Expr.evaluate_exists_oneTable existsContext inner database initial position outer conditionExists
      projectionsExists namesExists table outerRow present plainExists faultlessExists servedExists,
    any_kept_equals_iff inner equalsAffinity equalsCollation conditionIn conditionExists projection value _ link]
  refine ⟨?_, rfl, rfl⟩
  rw [truthy_inValue_eq_any inAffinity inCollation equalsAffinity equalsCollation value _
    (fun probeKnown candidate member => by
      obtain ⟨row, kept, rfl⟩ := List.mem_map.mp member
      obtain ⟨inRows, keeps⟩ := List.mem_filter.mp kept
      exact agree probeKnown row inRows keeps), truthy_truth]
  simp only [equalsValue_comm equalsAffinity equalsCollation value]

end Belay.Sqlite.Model.Resolved
