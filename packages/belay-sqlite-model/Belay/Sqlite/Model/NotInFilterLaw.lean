import Belay.Sqlite.Model.NotInSubqueryRun

set_option doc.verso true

/-! The filter law of {lit}`x NOT IN (SELECT c FROM u)` (task 20261027): for one row of an outer query, the
condition {lit}`x NOT IN (q)` and the condition {lit}`NOT EXISTS (q')`, with {lit}`q'` the correlated subquery
{lit}`SELECT 1 FROM u WHERE u.c = x`, have the same value and the same fault, when the premises of the value law hold
for the rows of {lit}`u`. The operand {lit}`x` is a column of the outer row, at the position {lit}`key`; a column cannot
fail, so {lit}`x` evaluates without fault. Both subqueries run without fault with certain rows, so the fault
of each condition is none. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context that serves subquery 0 with the run of {name}`Query.columnOf` for the outer row, every outer row and database with the table, the value of
{lit}`x NOT IN (SELECT c FROM u)` ({name}`Expr.inQuery`) is {name}`inValue` of the outer cell and of the cells of the
column {lit}`column` of the rows of the table, and its fault is none. Proof sketch: the run of the subquery has the
cells of the column as its rows, no fault and certain rows ({name}`Query.columnOf_subqueryRun`); the operand is a
column of the outer row, which has no fault. -/
theorem Expr.evaluate_inQuery_columnOf (context inner : EvalContext) (database : Database) (initial : Option Database)
    (position outer column key : Nat) (names : List String) (table : Table) (outerRow : List Value)
    (affinity : Option Affinity) (collation : Collation)
    (present : database.table position = some table)
    (served : context.subqueries 0 outerRow =
      (Query.columnOf position outer column names).subqueryRun inner database outerRow initial) :
    (Expr.inQuery (.column key) 0 affinity collation true).evaluate context outerRow =
      (inValue affinity collation true (outerRow.getD key .null)
        ((sourceRows table).map (fun cells => cells.getD column .null)), .none) := by
  obtain ⟨rows, fault, certain⟩ := Query.columnOf_subqueryRun inner database initial position outer column names table
    outerRow present
  simp only [Expr.evaluate, served, rows, fault, certain, Fault.join, ite_true, List.filterMap_map]
  simp [Function.comp_def]

/-- For every context that serves subquery 0 with the run of {name}`Query.matchingKey` for the outer row, every outer
row, key position inside the width {lit}`outer`, and database with the table, the value of
{lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` is 1 when no row of the table makes the comparison true
({name}`equalsValue`, with the table's cell as the left operand), else 0; its fault is none. Proof sketch: the run of the
subquery has one row for each row of the table that makes the comparison true, no fault
({name}`Query.matchingKey_subqueryRun`); it has a row exactly when some table row does. -/
theorem Expr.evaluate_notExists_matchingKey (context inner : EvalContext) (database : Database)
    (initial : Option Database) (position outer column key : Nat) (affinity : Option Affinity)
    (collation : Collation) (names : List String) (table : Table) (outerRow : List Value)
    (keyInside : key < outer) (present : database.table position = some table)
    (served : context.subqueries 0 outerRow =
      (Query.matchingKey position outer column key affinity collation names).subqueryRun inner database outerRow
        initial) :
    (Expr.not (.exists 0)).evaluate context outerRow =
      (truth (!(sourceRows table).any (fun cells =>
        truthy (equalsValue affinity collation (cells.getD column .null) (outerRow.getD key .null)))), .none) := by
  obtain ⟨rows, fault, _⟩ := Query.matchingKey_subqueryRun inner database initial position outer column key affinity
    collation names table outerRow keyInside present
  have empty : ((sourceRows table).filter (fun cells => truthy (equalsValue affinity collation
      (cells.getD column .null) (outerRow.getD key .null)))).isEmpty =
      !(sourceRows table).any (fun cells => truthy (equalsValue affinity collation (cells.getD column .null)
        (outerRow.getD key .null))) := by
    cases hany : (sourceRows table).any (fun cells => truthy (equalsValue affinity collation
      (cells.getD column .null) (outerRow.getD key .null)))
    · have none_ := List.any_eq_false.mp hany
      rw [List.filter_eq_nil_iff.mpr (by simpa using none_)]
      rfl
    · obtain ⟨cells, member, kept⟩ := List.any_eq_true.mp hany
      have present_ : cells ∈ (sourceRows table).filter (fun cells => truthy (equalsValue affinity collation
          (cells.getD column .null) (outerRow.getD key .null))) := List.mem_filter.mpr ⟨member, kept⟩
      rw [List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem present_)]
      rfl
  simp only [Expr.evaluate, served, rows, fault, List.isEmpty_map, empty]
  cases (sourceRows table).any (fun cells => truthy (equalsValue affinity collation (cells.getD column .null)
    (outerRow.getD key .null))) <;> rfl

/-- **Filter law.** For one outer row, with the key cell at position {lit}`key` inside the width {lit}`outer`, a context that serves
subquery 0 with {lit}`SELECT c FROM u` ({name}`Query.columnOf`) and a context that serves subquery 0 with
{lit}`SELECT 1 FROM u WHERE u.c = x` ({name}`Query.matchingKey`), over a database with the table {lit}`u`, the value and the
fault of {lit}`x NOT IN (SELECT c FROM u)` in the first context are the value and the fault of
{lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` in the second context, under these premises:
* the key cell is not NULL ({lit}`probe`);
* the cell of the column {lit}`c` is not NULL in any row of the table ({lit}`known`);
* for every row of the table, the {lit}`IN` test and the comparison {lit}`=` match its cell equally
  ({name}`inMatches`; {lit}`agree`).

Both conditions then have the same truth, so a {lit}`WHERE` keeps the row for both or for neither. Both have no fault
because the subqueries run without fault with certain rows and the key is a column of the outer row. When {lit}`probe` fails,
{lit}`NOT IN` of a table with a row is NULL and {lit}`NOT EXISTS` is 1; when {lit}`known` fails and no row matches,
{lit}`NOT IN` is NULL and {lit}`NOT EXISTS` is 1; so the law says nothing about those cases and the premises are not
dropped. When {lit}`agree` fails, the conditions can differ in the value as well. Proof sketch: the two evaluations
({name}`Expr.evaluate_inQuery_columnOf`, {name}`Expr.evaluate_notExists_matchingKey`) give {name}`inValue` and the
two-valued test; the value law ({name}`inValue_negated_eq_not_exists`) equates them, and the comparison commutes
({name}`equalsValue_comm`). -/
theorem Expr.evaluate_notIn_eq_notExists (inContext existsContext innerIn innerExists : EvalContext)
    (database : Database) (initial : Option Database) (position outer column key : Nat)
    (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation)
    (namesIn namesExists : List String) (table : Table) (outerRow : List Value)
    (keyInside : key < outer) (present : database.table position = some table)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.columnOf position outer column namesIn).subqueryRun innerIn database outerRow initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.matchingKey position outer column key equalsAffinity equalsCollation namesExists).subqueryRun
        innerExists database outerRow initial)
    (probe : (outerRow.getD key .null).isNull = false)
    (known : ∀ cells ∈ sourceRows table, (cells.getD column .null).isNull = false)
    (agree : ∀ cells ∈ sourceRows table,
      inMatches inAffinity inCollation (outerRow.getD key .null) (cells.getD column .null) =
        inMatches equalsAffinity equalsCollation (outerRow.getD key .null) (cells.getD column .null)) :
    (Expr.inQuery (.column key) 0 inAffinity inCollation true).evaluate inContext outerRow =
      (Expr.not (.exists 0)).evaluate existsContext outerRow := by
  rw [Expr.evaluate_inQuery_columnOf inContext innerIn database initial position outer column key namesIn table outerRow
      inAffinity inCollation present servedIn,
    Expr.evaluate_notExists_matchingKey existsContext innerExists database initial position outer column key
      equalsAffinity equalsCollation namesExists table outerRow keyInside present servedExists]
  congr 1
  rw [inValue_negated_eq_not_exists inAffinity inCollation equalsAffinity equalsCollation _ _ probe
    (by simpa using known) (by simpa using agree)]
  simp only [List.any_map, Function.comp_def, equalsValue_comm equalsAffinity equalsCollation (outerRow.getD key .null)]

end Belay.Sqlite.Model.Resolved
