import Belay.Sqlite.Programs.Scripts.DbDiagnostics
import Belay.Sqlite.Schema.Columns.SqlStatementContexts

set_option doc.verso true

/-! What the editor knows about the database at the start of each statement of a script: the
catalog and, when the run reached it, the stored rows. A context that only resolves its
statements ({lit}`resolvedContexts`, for {lit}`sql!`) knows the catalog from the resolution of
the statements before, and the rows of its database only until the first statement that can
change them. A context that runs its statements ({lit}`executedContexts`, for {lit}`db!` and
{lit}`#sql`) reads both from the connection that its run reached, so its rows are those of an
actual execution. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- The contexts of the statements of a script that runs, with the output of each statement that
ran: each context is the database of the connection that the run reached before the statement
({name}`runScriptStep`, with no values and no clock, as {name}`runDiagnosticsFrom` runs it). The
rows are those of that run. The lists end at the statement that ends the run, whose context is
the last one. -/
def executedContexts (index : Nat) (connection : Connection) :
    List (Located Syntax.Statement) → List StatementContext × List Output
  | [] => ([], [])
  | item :: rest =>
    let here : StatementContext :=
      { state := connection.resolveState, rows? := some connection.state.database.rows }
    match runScriptStep runContext none index connection item.value [] with
    | .ended _ => ([here], [])
    | .continued output next _ =>
      let later := executedContexts (index + 1) next rest
      (here :: later.1, output :: later.2)

end Belay.Sqlite
