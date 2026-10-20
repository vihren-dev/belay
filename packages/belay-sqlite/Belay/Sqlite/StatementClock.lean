import Belay.Sqlite.Resolution.Resolved
import Belay.Sqlite.ClockReads
import Belay.Sqlite.StoreValue
import Belay.Sqlite.JsonReady

set_option doc.verso true

/-! The clock of a resolved statement (ADR 0012, amendment 5, slice 6e2; ADR 0013, D6): the
cells of INSERT rows at the statement's clock value, and whether a statement reads the
clock at all. Evaluation takes the clock value as a parameter, so a statement is never
rewritten for a clock value. -/

namespace Belay.Sqlite.Resolved

/-- The value of an INSERT cell at a clock value, for a column of the affinity: a value
cell is its value, which resolution stored already; an expression cell is the value of its
expression at the clock value, which reads no column, stored with the affinity
({name}`storeValue`). -/
def Cell.valueAt (clock : Int) (affinity : Affinity) : Cell → Value
  | .value stored => stored
  | .expression term => storeValue affinity (term.eval clock [])

/-- The rows of an INSERT at a clock value: each cell's value ({name}`Cell.valueAt`) for the
affinity of its column; a cell past the last column has BLOB affinity. -/
def rowsAt (clock : Int) (columns : List CatalogColumn) (rows : List (List Cell)) : List (List Value) :=
  rows.map fun row => row.zipIdx.map fun (cell, index) =>
    cell.valueAt clock ((columns[index]?.map CatalogColumn.affinity).getD .blob)

/-- For every clock value, columns and rows whose cells are all values, the rows at the
clock value ({name}`rowsAt`) are those values: a script of known values reads no clock. -/
theorem rowsAt_values (clock : Int) (columns : List CatalogColumn) (rows : List (List Value)) :
    rowsAt clock columns (rows.map (·.map Cell.value)) = rows := by
  have cells : ∀ (row : List Value),
      (row.map Cell.value).zipIdx.map (fun (cell, index) =>
        cell.valueAt clock ((columns[index]?.map CatalogColumn.affinity).getD .blob)) = row := by
    intro row
    apply List.ext_getElem (by simp)
    intro index _ _
    simp [Cell.valueAt]
  simp only [rowsAt, List.map_map]
  conv => rhs; rw [← List.map_id rows]
  exact List.map_congr_left fun row _ => cells row

/-- The expression of an INSERT cell, if it has one. -/
def Cell.expression? : Cell → Option Expr
  | .value _ => none
  | .expression term => some term

/-- Every expression of a statement that evaluation reads: the expression cells of INSERT
rows ({name}`Cell.expression?`), the {lit}`RETURNING` columns, the values and filters of
writes, the clauses of an upsert ({name}`ConflictClause.expressions`) and the expressions
of a query ({name}`Query.expressions`); a schema or transaction statement and a prepare error
have none. -/
def Statement.clockExpressions : Statement → List Expr
  | .insert _ rows returning => rows.flatten.filterMap Cell.expression? ++ returning.map (·.1)
  | .upsert _ rows clauses returning _ =>
    rows.flatten.filterMap Cell.expression? ++ clauses.flatMap ConflictClause.expressions ++ returning.map (·.1)
  | .update _ assignments filter returning => assignments.map (·.2) ++ filter.toList ++ returning.map (·.1)
  | .delete _ filter returning => filter.toList ++ returning.map (·.1)
  | .query inner => inner.expressions
  | .createTable .. | .createIndex .. | .addColumn .. | .drop _ | .begin | .commit | .rollback | .prepareError _ => []

/-- Whether a statement reads the clock: it has an expression that reads it
({name}`Expr.readsClock`, {name}`Statement.clockExpressions`). The execution gives a
statement that does not the clock value 0, which it does not read ({lit}`runSqlAt`). -/
def Statement.readsClock (statement : Statement) : Bool :=
  statement.clockExpressions.any Expr.readsClock

end Belay.Sqlite.Resolved
