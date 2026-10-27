import Belay.Sqlite.Model.InSubqueryEqualityLink

set_option doc.verso true

/-! The filter laws of {lit}`x IN (SELECT c FROM u)` and {lit}`x NOT IN (SELECT c FROM u)` with columns (task
20261027): {lit}`x` is a column of the outer row and {lit}`c` is a column of the table {lit}`u`, with no
{lit}`WHERE` clause in the {lit}`IN` subquery. They are the instances of the filter laws of
{lit}`InSubqueryFilterLaw` for the correlated subquery {lit}`SELECT 1 FROM u WHERE u.c = x`. The premises are
facts about the cells of the outer row and of the table. -/

namespace Belay.Sqlite.Model.Resolved

/-- For one outer row, with the key cell at position {lit}`key` inside the width {lit}`outer`, a context that serves
subquery 0 with {lit}`SELECT c FROM u` and a context that serves subquery 0 with
{lit}`SELECT 1 FROM u WHERE u.c = x`, over a database with the table {lit}`u`, the value and the fault of
{lit}`x NOT IN (SELECT c FROM u)` are those of {lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)`, and the fault of
both is none, under these premises:
* the key cell is not NULL ({lit}`probe`);
* the cell of the column {lit}`c` is not NULL in any row of the table ({lit}`known`);
* for every row of the table, the {lit}`IN` test and the comparison {lit}`=` match its cell equally
  ({name}`inMatches`; {lit}`agree`).

The cases in which a premise fails are in {name}`Expr.evaluate_notIn_eq_notExists`: there {lit}`NOT IN` can be NULL
where {lit}`NOT EXISTS` is 1. Proof sketch: the instance of {name}`Expr.evaluate_notIn_eq_notExists` with the columns
as expressions; the joined rows have the outer cell and the table cell at the positions ({name}`joinedRows_getD_outer`,
{name}`joinedRows_getD_cell`), the link is {name}`correlatedEquality_of_compare`, and column reads have no fault. -/
theorem Expr.evaluate_notIn_eq_notExists_of_columns (inContext existsContext inner : EvalContext)
    (database : Database) (initial : Option Database) (position outer column key : Nat)
    (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation)
    (namesIn namesExists : List String) (table : Table) (outerRow : List Value) (keyInside : key < outer)
    (present : database.table position = some table)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer none [.column (outer + column)] namesIn).subqueryRun inner database outerRow
        initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer
        (some (.compare .eq equalsAffinity (.column (outer + column)) (.column key) equalsCollation))
        [.literal (.integer 1)] namesExists).subqueryRun inner database outerRow initial)
    (probe : (outerRow.getD key .null).isNull = false)
    (known : ∀ cells ∈ sourceRows table, (cells.getD column .null).isNull = false)
    (agree : ∀ cells ∈ sourceRows table,
      inMatches inAffinity inCollation (outerRow.getD key .null) (cells.getD column .null) =
        inMatches equalsAffinity equalsCollation (outerRow.getD key .null) (cells.getD column .null)) :
    (Expr.inQuery (.column key) 0 inAffinity inCollation true).evaluate inContext outerRow =
        (Expr.not (.exists 0)).evaluate existsContext outerRow ∧
      ((Expr.inQuery (.column key) 0 inAffinity inCollation true).evaluate inContext outerRow).2 = .none := by
  refine Expr.evaluate_notIn_eq_notExists inContext existsContext inner database initial position outer none _
    (.column (outer + column)) (.column key) _ namesIn namesExists table outerRow inAffinity equalsAffinity inCollation
    equalsCollation (outerRow.getD key .null) present (by simp [Expr.any, Expr.isFallibleCall])
    (by simp [Expr.evaluate]) (by simp [Expr.any, Expr.isFallibleCall])
    (by simp [Expr.evaluate, Fault.join]) servedIn servedExists rfl probe ?_ ?_
    (correlatedEquality_of_compare inner equalsAffinity equalsCollation _ _ _ _ fun row member => by
      rw [Expr.eval_column, joinedRows_getD_outer member keyInside])
  · intro row member _
    obtain ⟨cells, inRows, cell⟩ := joinedRows_getD_cell member column
    rw [Expr.eval_column, cell]
    exact known cells inRows
  · intro row member _
    obtain ⟨cells, inRows, cell⟩ := joinedRows_getD_cell member column
    rw [Expr.eval_column, cell]
    exact agree cells inRows

/-- For the same outer row, contexts and database, the truth of {lit}`x IN (SELECT c FROM u)` is the truth of
{lit}`EXISTS (SELECT 1 FROM u WHERE u.c = x)`, and neither has a fault, under one premise: for every row of the table,
the {lit}`IN` test and the comparison {lit}`=` match its cell equally when the key cell is not NULL
({name}`inMatches`; {lit}`agree`). A NULL key cell or a NULL cell of {lit}`c` needs no premise: neither is true for
{lit}`IN` or for the comparison. The values can differ: {lit}`IN` can be NULL where {lit}`EXISTS` is 0. Proof sketch: the
instance of {name}`Expr.evaluate_in_truthy_eq_exists`, as for {name}`Expr.evaluate_notIn_eq_notExists_of_columns`. -/
theorem Expr.evaluate_in_truthy_eq_exists_of_columns (inContext existsContext inner : EvalContext)
    (database : Database) (initial : Option Database) (position outer column key : Nat)
    (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation)
    (namesIn namesExists : List String) (table : Table) (outerRow : List Value) (keyInside : key < outer)
    (present : database.table position = some table)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer none [.column (outer + column)] namesIn).subqueryRun inner database outerRow
        initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer
        (some (.compare .eq equalsAffinity (.column (outer + column)) (.column key) equalsCollation))
        [.literal (.integer 1)] namesExists).subqueryRun inner database outerRow initial)
    (agree : (outerRow.getD key .null).isNull = false → ∀ cells ∈ sourceRows table,
      inMatches inAffinity inCollation (outerRow.getD key .null) (cells.getD column .null) =
        inMatches equalsAffinity equalsCollation (outerRow.getD key .null) (cells.getD column .null)) :
    truthy ((Expr.inQuery (.column key) 0 inAffinity inCollation false).evaluate inContext outerRow).1 =
        truthy ((Expr.exists 0).evaluate existsContext outerRow).1 ∧
      ((Expr.inQuery (.column key) 0 inAffinity inCollation false).evaluate inContext outerRow).2 = .none ∧
      ((Expr.exists 0).evaluate existsContext outerRow).2 = .none := by
  refine Expr.evaluate_in_truthy_eq_exists inContext existsContext inner database initial position outer none _
    (.column (outer + column)) (.column key) _ namesIn namesExists table outerRow inAffinity equalsAffinity inCollation
    equalsCollation (outerRow.getD key .null) present (by simp [Expr.any, Expr.isFallibleCall])
    (by simp [Expr.evaluate]) (by simp [Expr.any, Expr.isFallibleCall])
    (by simp [Expr.evaluate, Fault.join]) servedIn servedExists rfl ?_
    (correlatedEquality_of_compare inner equalsAffinity equalsCollation _ _ _ _ fun row member => by
      rw [Expr.eval_column, joinedRows_getD_outer member keyInside])
  intro probe row member _
  obtain ⟨cells, inRows, cell⟩ := joinedRows_getD_cell member column
  rw [Expr.eval_column, cell]
  exact agree probe cells inRows

/-- For every outer row of any length, every context that serves subquery 0 with {lit}`SELECT c FROM u`
({name}`Query.oneTable`), and either polarity, the fault of {lit}`x IN (SELECT c FROM u)` is none. The subquery runs
without fault with certain rows, and the probe is a column. The value is {name}`inValue` of the outer cell and the
column cells, as {name}`Expr.evaluate_inQuery_oneTable` states. Proof sketch: the instance of
{name}`Expr.evaluate_inQuery_oneTable` with the columns; column reads have no fault. -/
theorem Expr.fault_inQuery_of_columns (inContext inner : EvalContext) (database : Database)
    (initial : Option Database) (position outer column key : Nat) (affinity : Option Affinity)
    (collation : Collation) (negated : Bool) (names : List String) (table : Table) (outerRow : List Value)
    (present : database.table position = some table)
    (served : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer none [.column (outer + column)] names).subqueryRun inner database outerRow
        initial) :
    ((Expr.inQuery (.column key) 0 affinity collation negated).evaluate inContext outerRow).2 = .none := by
  rw [Expr.evaluate_inQuery_oneTable inContext inner database initial position outer none (.column (outer + column))
    (.column key) names table outerRow affinity collation negated (outerRow.getD key .null) present
    (by simp [Expr.any, Expr.isFallibleCall]) (by simp [Expr.evaluate]) served rfl]

/-- For every outer row of any length, every context that serves subquery 0 with
{lit}`SELECT 1 FROM u WHERE u.c = x` ({name}`Query.oneTable`), the fault of {lit}`EXISTS` of it is none, and so is the
fault of {lit}`NOT EXISTS` of it. Proof sketch: the instances of {name}`Expr.evaluate_exists_oneTable` and
{name}`Expr.evaluate_notExists_oneTable` with the comparison of two columns. -/
theorem Expr.fault_exists_of_columns (existsContext inner : EvalContext) (database : Database)
    (initial : Option Database) (position outer column key : Nat) (affinity : Option Affinity)
    (collation : Collation) (names : List String) (table : Table) (outerRow : List Value)
    (present : database.table position = some table)
    (served : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer (some (.compare .eq affinity (.column (outer + column)) (.column key) collation))
        [.literal (.integer 1)] names).subqueryRun inner database outerRow initial) :
    ((Expr.exists 0).evaluate existsContext outerRow).2 = .none ∧
      ((Expr.not (.exists 0)).evaluate existsContext outerRow).2 = .none := by
  constructor
  · rw [Expr.evaluate_exists_oneTable existsContext inner database initial position outer _ _ names table outerRow
      present (by simp [Expr.any, Expr.isFallibleCall]) (by simp [Expr.evaluate, Fault.join]) served]
  · rw [Expr.evaluate_notExists_oneTable existsContext inner database initial position outer _ _ names table outerRow
      present (by simp [Expr.any, Expr.isFallibleCall]) (by simp [Expr.evaluate, Fault.join]) served]

end Belay.Sqlite.Model.Resolved
