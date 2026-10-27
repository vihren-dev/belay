import Belay.Sqlite.Model.ExprAppendLaws
import Belay.Sqlite.Model.SimpleResultsLaws

set_option doc.verso true

/-!
A simple query that reads only old columns (ADR 0017, S6). A simple query has a filter and scalar
result columns and no grouping, ordering, window or aggregate. When every expression of the query reads
only columns below a width, the cells that a migration appends to the rows of that width cannot change
the query's results. This is the semantic fact behind a dependency certificate of a read: the
certificate lists the columns that the read uses, and the fact says that columns outside the list
cannot matter.
-/

namespace Belay.Sqlite.Model.Resolved

/-- Whether a result column reads only columns below the width: a scalar expression that does
({name}`Expr.readsBelow`). An aggregate column never qualifies, so the check is conservative. For
example, the column {lit}`a + 1` over the columns {lit}`a, b` reads below width 1, and the column
{lit}`b` does not. -/
def Output.readsBelow (width : Nat) : Output → Bool
  | .scalar expression => expression.readsBelow width
  | .aggregate _ => false

/-- For every context that does not depend on the outer row, row with at least {lit}`width` cells, cells to
append and optional filter that reads only columns below the width: the filter keeps the row with the cells
appended exactly when it keeps the row. A missing filter keeps every row. Proof sketch: the filter keeps its
value under appended cells ({name}`Expr.eval_append`). -/
theorem Query.filterKeeps_append (context : EvalContext) (rowFree : context.RowFree) (row extra : List Value)
    (width : Nat) (wide : width ≤ row.length) (filter : Option Expr)
    (below : ∀ condition ∈ filter, condition.readsBelow width = true) :
    (filter.all fun condition => truthy (condition.eval context (row ++ extra))) =
      (filter.all fun condition => truthy (condition.eval context row)) := by
  cases filter with
  | none => rfl
  | some condition =>
    simp only [Option.all_some]
    rw [Expr.eval_append context rowFree row extra wide (below condition rfl)]

/-- For every context whose subqueries do not depend on the outer row, rows with at least {lit}`width` cells,
function that gives the cells to append to a row, two simple queries that return the same result columns, all
below the width, and any sources and names: if for each row the filter of the second query on the row with
its appended cells keeps the row exactly when the filter of the first query keeps the row, then the second
query over the rows with their cells appended has the results of the first query over the rows. In plain
words, the two filters may be different expressions, and the second may read the appended cells; the
statement requires only that they keep the same rows. A missing filter keeps every row. The names of the
result columns play no part. Proof sketch: a simple query keeps the rows whose filter is true and maps each kept
row to its columns ({name}`Query.Simple.results_eq`); the kept rows agree by the premise, and each result
column keeps its value under appended cells ({name}`Expr.eval_append`). -/
theorem Query.simple_results_agree (context : EvalContext) (rowFree : context.RowFree)
    (rows : List (List Value)) (extra : List Value → List Value) (beforeSources afterSources : List QuerySource)
    (beforeFilter afterFilter : Option Expr) (columns : List Output) (beforeNames afterNames : List String)
    (width : Nat) (wide : ∀ row ∈ rows, width ≤ row.length)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true)
    (agree : ∀ row ∈ rows,
      (afterFilter.all fun condition => truthy (condition.eval context (row ++ extra row))) =
        (beforeFilter.all fun condition => truthy (condition.eval context row))) :
    (Query.simple afterSources afterFilter columns afterNames).results context
        (rows.map fun row => row ++ extra row) =
      (Query.simple beforeSources beforeFilter columns beforeNames).results context rows := by
  rw [(Query.simple_isSimple ..).results_eq, (Query.simple_isSimple ..).results_eq]
  simp only [filtered, Query.simple]
  rw [List.filter_map, List.map_map]
  have kept : rows.filter ((fun row => afterFilter.all fun condition => truthy (condition.eval context row)) ∘
      fun row => row ++ extra row) =
      rows.filter fun row => beforeFilter.all fun condition => truthy (condition.eval context row) :=
    List.filter_congr fun row member => agree row member
  rw [kept]
  refine List.map_congr_left fun row member => ?_
  have member := (List.mem_filter.mp member).1
  simp only [Function.comp_apply]
  refine List.map_congr_left fun column inColumns => ?_
  cases column with
  | scalar expression =>
    exact Expr.eval_append context rowFree row (extra row) (wide row member) (columnsBelow _ inColumns)
  | aggregate _ => exact absurd (columnsBelow _ inColumns) (by simp [Output.readsBelow])

/-- For every context whose subqueries do not depend on the outer row, rows with at least {lit}`width` cells,
function that gives the cells to append to a row, simple query whose filter and result columns read only
columns below the width, and any two lists of result names: the results of the query over the rows with
their cells appended are the results of the query over the rows. In plain words, appended cells change
neither which rows the filter keeps nor the values of the result columns. The names of the result
columns play no part. Proof sketch: the case of {name}`Query.simple_results_agree` with the same filter on both
sides, whose rows agree because the filter reads below the width ({name}`Query.filterKeeps_append`). -/
theorem Query.simple_results_append (context : EvalContext) (rowFree : context.RowFree)
    (rows : List (List Value)) (extra : List Value → List Value) (sources : List QuerySource)
    (filter : Option Expr) (columns : List Output) (names other : List String) (width : Nat)
    (wide : ∀ row ∈ rows, width ≤ row.length)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow width = true)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true) :
    (Query.simple sources filter columns other).results context (rows.map fun row => row ++ extra row) =
      (Query.simple sources filter columns names).results context rows := by
  exact Query.simple_results_agree context rowFree rows extra sources sources filter filter columns names other
    width wide columnsBelow fun row member =>
      Query.filterKeeps_append context rowFree row (extra row) width (wide row member) filter filterBelow

end Belay.Sqlite.Model.Resolved
