import Belay.Sqlite.Model.NormalizedFieldRows
import Belay.Sqlite.Model.SimpleResultsLaws

set_option doc.verso true

/-! Query-result laws for an appended lowercase field. Parameters retain every
{name}`Belay.Sqlite.Model.Value` constructor. These laws describe the existing
simple query evaluator; the migration proof must derive its input rows. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- The original predicate {lit}`lower(column) = lower(parameter)`, with resolved
column and one-based parameter positions. Function expressions supply no
comparison affinity and use default BINARY collation. -/
def originalFilter (source parameter : Nat) : Expr :=
  .compare .eq none (.scalar .lower (.cons (.column source) .nil))
    (.scalar .lower (.cons (.parameter parameter) .nil))

/-- The translated predicate {lit}`stored_column = lower(parameter)`. The stored
column supplies TEXT affinity and default BINARY collation. Use the appended
column's actual resolved position for {lit}`stored`. -/
def storedFilter (stored parameter : Nat) : Expr :=
  .compare .eq (some .text) (.column stored)
    (.scalar .lower (.cons (.parameter parameter) .nil))

/-- For every context, row and parameter position, reading an appended lowercase
cell gives the same predicate value as computing lowercase from its original
source value, which is NULL past the row's end. The parameter can be absent,
NULL or any other value. Proof sketch:
the appended cell is the lowercase result and TEXT affinity changes neither
lowercase operand. -/
theorem storedFilter_append (context : EvalContext) (row : List Value)
    (width source parameter : Nat) (wide : row.length = width) :
    (storedFilter width parameter).eval context
        (row ++ [mapText lowerByte (row.getD source .null)]) =
      (originalFilter source parameter).eval context row := by
  have cell : (row ++ [mapText lowerByte (row.getD source .null)]).getD width .null =
      mapText lowerByte (row.getD source .null) := by
    simp [← wide, List.getD_eq_getElem?_getD]
  simp only [storedFilter, originalFilter, Expr.eval_compare, Expr.eval_column,
    Expr.eval_parameter, eval_lower, cell, comparisonOperands_lower]
  rfl

/-- For every context, row and parameter position, the original lowercase
predicate keeps its value after any cells are appended, provided its source
position is inside the original row. Proof sketch: its column still reads the
same cell and its parameter does not read the row. -/
theorem originalFilter_append (context : EvalContext) (row extra : List Value)
    (source parameter : Nat) (inside : source < row.length) :
    (originalFilter source parameter).eval context (row ++ extra) =
      (originalFilter source parameter).eval context row := by
  simp [originalFilter, Expr.eval_compare, Expr.eval_column, Expr.eval_parameter,
    eval_lower, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]

/-- If two predicates agree on each original and extended row, their simple
SELECT of an unchanged column has the same results. Proof sketch: move the map
through the filter, identify the filters, then identify each projected cell. -/
private theorem simple_results_append (context : EvalContext) (rows : List (List Value))
    (extra : List Value → List Value) (beforeSources afterSources : List QuerySource)
    (before after : Expr) (column width : Nat)
    (wide : ∀ row ∈ rows, row.length = width) (inside : column < width)
    (same : ∀ row ∈ rows, after.eval context (row ++ extra row) = before.eval context row) :
    (Query.simple afterSources (some after) [.scalar (.column column)] ["id"]).results
        context (rows.map fun row => row ++ extra row) =
      (Query.simple beforeSources (some before) [.scalar (.column column)] ["id"]).results context rows := by
  rw [(Query.simple_isSimple ..).results_eq, (Query.simple_isSimple ..).results_eq]
  simp only [filtered, Query.simple, Option.all_some, List.map_cons, List.map_nil, Expr.eval_column]
  rw [List.filter_map, List.map_map]
  simp only [Function.comp_def]
  have kept : rows.filter (fun row => truthy (after.eval context (row ++ extra row))) =
      rows.filter (fun row => truthy (before.eval context row)) :=
    List.filter_congr fun row member => congrArg truthy (same row member)
  rw [kept]
  apply List.map_congr_left
  intro row member
  have member := (List.mem_filter.mp member).1
  have below : column < row.length := by rw [wide row member]; exact inside
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left below]

/-- For every context, arbitrary equally wide rows and parameter position,
SELECT of an existing ID column using the stored lowercase field has exactly
the original lowercase query's results on the original rows. Each new row must
be the original row with its computed lowercase value appended; this theorem
does not assert that a migration produced those rows. There is no restriction
on parameter values or row count. Proof sketch: the derived per-row predicate
equality and unchanged ID cells give equality through filtering and projection. -/
theorem results_translate (context : EvalContext) (rows : List (List Value))
    (beforeSources afterSources : List QuerySource) (width source id parameter : Nat)
    (wide : ∀ row ∈ rows, row.length = width) (idInside : id < width) :
    (Query.simple afterSources (some (storedFilter width parameter)) [.scalar (.column id)] ["id"]).results
        context (rows.map fun row => row ++ [mapText lowerByte (row.getD source .null)]) =
      (Query.simple beforeSources (some (originalFilter source parameter))
        [.scalar (.column id)] ["id"]).results context rows := by
  apply simple_results_append context rows _ beforeSources afterSources _ _ id width wide idInside
  intro row member
  exact storedFilter_append context row width source parameter (wide row member)

/-- For every context, arbitrary equally wide rows and parameter position,
the original lowercase query keeps its exact ID results after a lowercase cell
is appended to each row, when both original column positions are in range.
The statement covers NULL and nontext cells and parameters. Proof sketch:
the original predicate and projected ID read only unchanged original cells. -/
theorem results_preserve (context : EvalContext) (rows : List (List Value))
    (beforeSources afterSources : List QuerySource) (width source id parameter : Nat)
    (wide : ∀ row ∈ rows, row.length = width) (sourceInside : source < width) (idInside : id < width) :
    (Query.simple afterSources (some (originalFilter source parameter)) [.scalar (.column id)] ["id"]).results
        context (rows.map fun row => row ++ [mapText lowerByte (row.getD source .null)]) =
      (Query.simple beforeSources (some (originalFilter source parameter))
        [.scalar (.column id)] ["id"]).results context rows := by
  apply simple_results_append context rows _ beforeSources afterSources _ _ id width wide idInside
  intro row member
  exact originalFilter_append context row _ source parameter (by rw [wide row member]; exact sourceInside)

end Belay.Sqlite.Model.NormalizedField
