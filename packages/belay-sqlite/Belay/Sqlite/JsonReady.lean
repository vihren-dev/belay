import Belay.Sqlite.QueryRun
import Belay.Sqlite.RowUpdate
import Belay.Sqlite.Resolution.ConflictForm

set_option doc.verso true

/-! Where the model describes the JSON failures of a statement (ADR 0012, amendment 5,
slice 6b), as a part of the supported-subset check {lit}`statementReady`. A query is
ready when the fault of its run is not {lit}`may` ({lit}`Query.run`). A write is ready only when no
JSON call of its conditions and values may fail: the model gives a write no JSON error.
Each check also evaluates the expressions over the row with no cells, which reads NULL
in every column, because SQLite evaluates a constant {lit}`WHERE` term once before it
reads the rows. -/

namespace Belay.Sqlite

/-- The {lit}`RETURNING` expressions of a write. -/
def returningExpressions (returning : List (Resolved.Expr × String)) : List Resolved.Expr :=
  returning.map (·.1)

/-- Whether an UPDATE over the table is ready: no JSON call of {lit}`WHERE` may fail
over a row of the table or over the empty row, no JSON call of a {lit}`SET` value may
fail over a row that {lit}`WHERE` selects, and no {lit}`RETURNING` expression has a JSON
call. -/
def updateJsonReady (clock : Int) (table : Table) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) : Bool :=
  let rows := table.rows.map Row.values
  let chosen := (table.rows.filter (LiteralData.selected clock filter)).map Row.values
  !Resolved.anyMayFail clock ([] :: rows) filter.toList &&
  !Resolved.anyMayFail clock chosen (assignments.map (·.2)) &&
  !(returningExpressions returning).any (·.any Resolved.Expr.isJsonCall)

/-- Whether a DELETE over the table is ready: no JSON call of {lit}`WHERE` may fail over
a row of the table or over the empty row, and no {lit}`RETURNING` expression has a JSON
call. -/
def deleteJsonReady (clock : Int) (table : Table) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) : Bool :=
  !Resolved.anyMayFail clock ([] :: table.rows.map Row.values) filter.toList &&
  !(returningExpressions returning).any (·.any Resolved.Expr.isJsonCall)

/-- The expressions of an {lit}`ON CONFLICT` clause: the values and the filter of
{lit}`DO UPDATE`; none for {lit}`DO NOTHING`. -/
def Resolved.ConflictClause.expressions (clause : Resolved.ConflictClause) : List Resolved.Expr :=
  match clause.action with
  | .nothing => []
  | .update assignments filter => assignments.map (·.2) ++ filter.toList

/-- Whether an INSERT with {lit}`ON CONFLICT` clauses is ready: no clause and no
{lit}`RETURNING` expression has a JSON call. -/
def upsertJsonReady (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String)) :
    Bool :=
  !(clauses.flatMap Resolved.ConflictClause.expressions ++ returningExpressions returning).any
    (·.any Resolved.Expr.isJsonCall)

end Belay.Sqlite
