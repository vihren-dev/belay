import Belay.Sqlite.Model.CorrelatedSubquerySource

set_option doc.verso true

/-! The run of a simple subquery of one table for one row of an outer query (task 20261027). A subquery row is the
outer row followed by the cells of a row of the subquery's table, so a subquery reads the outer cells at their own
positions and its own cells after the width {lit}`outer` of the outer query. The module is general over the table
position, the width, an optional {lit}`WHERE` expression and the result expressions, so it covers
{lit}`SELECT c FROM u`, {lit}`SELECT 1 FROM u WHERE u.c = x`, a subquery with a {lit}`WHERE` clause, and any result
expression. It has no fact about a catalog. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether an optional {lit}`WHERE` expression keeps a row in a context: there is no expression, or the expression is
true for the row. It is the test of {name}`filtered`. -/
def conditionKeeps (condition : Option Expr) (context : EvalContext) (row : List Value) : Bool :=
  condition.all fun expression => truthy (expression.eval context row)

/-- The rows of a subquery of one table for one outer row, before the condition: each row of the table in scan order after
the outer cells ({name}`outerCells`) of the width {lit}`outer`. -/
def joinedRows (outer : Nat) (outerRow : List Value) (table : Table) : List (List Value) :=
  (sourceRows table).map fun cells => outerCells outer outerRow ++ cells

/-- The simple subquery of one table at a position: its only source is the table, it has the optional {lit}`WHERE`
expression, and its result columns are the given expressions. The rows of the outer query have {lit}`outer` cells, and
they come first in a row of the subquery, so the cells of the table start at position {lit}`outer`. With the width
{lit}`outer = 0` it is a top-level query of one table. -/
def Query.oneTable (table outer : Nat) (condition : Option Expr) (projections : List Expr) (names : List String) :
    Query :=
  { Query.simple [QuerySource.first table] condition (projections.map .scalar) names with outer }

/-- For every table position, width, condition, result expressions and names, the query {name}`Query.oneTable` is
simple ({name}`Query.Simple`). Proof sketch: it is {name}`Query.simple` with another width of the outer row. -/
theorem Query.oneTable_simple (table outer : Nat) (condition : Option Expr) (projections : List Expr)
    (names : List String) : (Query.oneTable table outer condition projections names).Simple :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The expressions of the query {name}`Query.oneTable` are its condition and its result expressions. Proof sketch:
unfold the expressions of the query; the one source has no condition and no argument. -/
theorem Query.oneTable_expressions (table outer : Nat) (condition : Option Expr) (projections : List Expr)
    (names : List String) :
    (Query.oneTable table outer condition projections names).expressions = condition.toList ++ projections := by
  simp [Query.oneTable, Query.simple, Query.expressions, Query.keptExpressions, Output.scalars, Output.operands,
    QuerySource.expressions, QuerySource.first, List.flatMap_map]

/-- For every outer row, every database with the table at the position, every context and optional initial
database, the subquery {name}`Query.oneTable` run for the outer row has, as its rows, one row for each joined row
({name}`joinedRows`) that the condition keeps ({name}`conditionKeeps`), with the values of the result expressions; it
has no fault, and its rows are certain. The expressions read the outer cells followed by the cells of the table row.
The outer row can have any length: the subquery sees it cut or filled with NULL to the width {lit}`outer`. The premises
are that no expression has a fallible call ({lit}`plain`) and that none has a fault over the empty row and over each
joined row ({lit}`faultless`); a premise that fails is not assumed. Proof sketch: the source rows are the joined rows
({name}`Query.sourceAfter_first`); the simple query has no fault ({name}`Query.subqueryRun_simple_after`); its result is
the filtered rows with the result expressions ({name}`Query.Simple.results_eq`). -/
theorem Query.oneTable_subqueryRun (context : EvalContext) (database : Database) (initial : Option Database)
    (position outer : Nat) (condition : Option Expr) (projections : List Expr) (names : List String) (table : Table)
    (outerRow : List Value) (present : database.table position = some table)
    (plain : ∀ expression ∈ condition.toList ++ projections, expression.any Expr.isFallibleCall = false)
    (faultless : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ condition.toList ++ projections, (expression.evaluate context row).2 = .none) :
    ((Query.oneTable position outer condition projections names).subqueryRun context database outerRow initial).rows =
        ((joinedRows outer outerRow table).filter (conditionKeeps condition context)).map (fun row =>
          projections.map (fun expression => expression.eval context row)) ∧
      ((Query.oneTable position outer condition projections names).subqueryRun context database outerRow
        initial).fault = .none ∧
      ((Query.oneTable position outer condition projections names).subqueryRun context database outerRow
        initial).rowsCertain = true := by
  have found := Query.sourceAfter_first context database initial (Query.oneTable position outer condition projections names)
    position table outerRow rfl present
  have run := Query.subqueryRun_simple_after context database initial outerRow _
    (Query.oneTable_simple position outer condition projections names) _ found rfl
    (List.all_eq_true.mpr fun expression inside => by
      rw [Query.oneTable_expressions] at inside
      simp [plain expression inside])
    (fun row member expression inside => by
      rw [Query.oneTable_expressions] at inside
      exact faultless row member expression inside)
  rw [run]
  refine ⟨?_, rfl, rfl⟩
  rw [(Query.oneTable_simple position outer condition projections names).results_eq]
  simp [filtered, joinedRows, Query.oneTable, Query.simple, Function.comp_def]
  rfl

end Belay.Sqlite.Model.Resolved
