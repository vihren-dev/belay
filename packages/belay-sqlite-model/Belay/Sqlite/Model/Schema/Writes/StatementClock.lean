import Belay.Sqlite.Model.Schema.Writes.JsonReady
import Belay.Sqlite.Model.Queries.Evaluation.StatementClock

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- The rows of an INSERT in an evaluation context: each cell's value ({name}`Cell.valueAt`) for the
affinity of its column; a cell past the last column has BLOB affinity. -/
def rowsAt (context : EvalContext) (columns : List CatalogColumn) (rows : List (List Cell)) : List (List Value) :=
  rows.map fun row => row.zipIdx.map fun (cell, index) =>
    cell.valueAt context ((columns[index]?.map CatalogColumn.affinity).getD .blob)

/-- For every evaluation context, columns and rows whose cells are all values, the rows in
the context ({name}`rowsAt`) are those values: a script of known values reads nothing of the
context. -/
theorem rowsAt_values (context : EvalContext) (columns : List CatalogColumn) (rows : List (List Value)) :
    rowsAt context columns (rows.map (·.map Cell.value)) = rows := by
  have cells : ∀ (row : List Value),
      (row.map Cell.value).zipIdx.map (fun (cell, index) =>
        cell.valueAt context ((columns[index]?.map CatalogColumn.affinity).getD .blob)) = row := by
    intro row
    apply List.ext_getElem (by simp)
    intro index _ _
    simp [Cell.valueAt]
  simp only [rowsAt, List.map_map]
  conv => rhs; rw [← List.map_id rows]
  exact List.map_congr_left fun row _ => cells row

/-- Whether no expression cell of the rows of an INSERT may fail in the statement's context,
over the row without cells that SQLite evaluates them over: a subquery that it names has a
value that the model describes ({name}`Resolved.Fault.may` otherwise). -/
def cellsReady (context : Resolved.EvalContext) (rows : List (List Resolved.Cell)) : Bool :=
  !Resolved.anyMayFail context [[]] (rows.flatten.filterMap Resolved.Cell.expression?)

end Belay.Sqlite.Model.Resolved
