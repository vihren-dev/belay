import Belay.Sqlite.Model.Schema.Rows.AdmittedPlainWrites
import Belay.Sqlite.Model.Schema.Writes.AdmittedUpdatedTable
import Belay.Sqlite.Model.Schema.Rows.AdmittedWriteReady

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every limits, clock value, counters, parameter list, target, assignments, filter, returning list
and subqueries, and every database whose rows are aliased and whose catalog is valid under the limits:
the effect of a plain UPDATE satisfies "rows aliased" ({name}`Effect.Satisfies`): the alias cell of every
row is the integer rowid. Any error other than {name}`ExecutionError.constraintFail` requires nothing.
The statement does not need to be ready. Proof sketch: a valid catalog does not generate the alias
column ({name}`Database.aliasUngenerated`); an UPDATE that stores a table has no refused alias
({name}`runStatement_update_atom`), so {name}`LiteralData.updated_aliased` applies. -/
theorem runStatement_update_rowsAliased (limits : Limits) (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) {database : Database} (aliased : database.RowsAliased)
    (valid : database.catalog.Valid limits) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none)
      database).effect.Satisfies Database.RowsAliased :=
  runStatement_update_atom (atom := Table.RowsAliased) clock counters parameters target assignments filter
    returning subqueries aliased fun _ found accepted _ =>
      LiteralData.updated_aliased (aliased _ _ found) (Database.aliasUngenerated valid found) accepted

end Belay.Sqlite.Model
