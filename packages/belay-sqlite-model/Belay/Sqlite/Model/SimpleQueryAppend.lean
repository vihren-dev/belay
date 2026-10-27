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

/-- For every context whose subqueries do not depend on the outer row, rows with at least {lit}`width` cells,
function that gives the cells to append to a row, simple query whose filter and result columns read only
columns below the width, and any two lists of result names: the results of the query over the rows with
their cells appended are the results of the query over the rows. In plain words, appended cells change
neither which rows the filter keeps nor the values of the result columns. The names of the result
columns play no part. Proof sketch: a simple query keeps the rows whose filter is true and maps each kept
row to its columns ({name}`Query.Simple.results_eq`); each expression keeps its value under appended cells
({name}`Expr.eval_append`), so the filtered rows and their cells agree. -/
theorem Query.simple_results_append (context : EvalContext) (rowFree : context.RowFree)
    (rows : List (List Value)) (extra : List Value → List Value) (sources : List QuerySource)
    (filter : Option Expr) (columns : List Output) (names other : List String) (width : Nat)
    (wide : ∀ row ∈ rows, width ≤ row.length)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow width = true)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true) :
    (Query.simple sources filter columns other).results context (rows.map fun row => row ++ extra row) =
      (Query.simple sources filter columns names).results context rows := by
  rw [(Query.simple_isSimple ..).results_eq, (Query.simple_isSimple ..).results_eq]
  simp only [filtered, Query.simple]
  rw [List.filter_map, List.map_map]
  have kept : rows.filter ((fun row => filter.all fun condition => truthy (condition.eval context row)) ∘
      fun row => row ++ extra row) = rows.filter fun row => filter.all fun condition => truthy (condition.eval context row) := by
    refine List.filter_congr fun row member => ?_
    cases filter with
    | none => rfl
    | some condition =>
      simp only [Function.comp_apply, Option.all_some]
      rw [Expr.eval_append context rowFree row (extra row) (wide row member) (filterBelow condition rfl)]
  rw [kept]
  refine List.map_congr_left fun row member => ?_
  have member := (List.mem_filter.mp member).1
  simp only [Function.comp_apply]
  refine List.map_congr_left fun column inColumns => ?_
  cases column with
  | scalar expression =>
    exact Expr.eval_append context rowFree row (extra row) (wide row member) (columnsBelow _ inColumns)
  | aggregate _ => exact absurd (columnsBelow _ inColumns) (by simp [Output.readsBelow])

end Belay.Sqlite.Model.Resolved
