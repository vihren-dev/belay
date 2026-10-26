import Belay.Sqlite.Run
import Belay.Sqlite.Translation
import Belay.Sqlite.SqlDiagnostics
import Belay.Sqlite.DbDiagnostics

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

/-- The database at the start of a statement, as far as the editor knows it. For example,
{lean}`({ catalog := [], rows? := none } : StatementContext)` knows no table and no rows. -/
structure StatementContext where
  /-- The catalog at the start of the statement. -/
  catalog : Catalog
  /-- The stored rows of each catalog position at the start of the statement, or none when an
  earlier statement may have changed them and no run measured them. -/
  rows? : Option (List (List Row))

/-- Whether the statement can change the stored rows of a table, or the catalog positions that
index them, so that rows known before it are not known after it. Every statement that writes, and
every statement that creates, drops or alters a catalog object, counts: a dropped view or index
moves the positions of the objects after it. Only a query, a transaction statement and a pragma
leave the rows as they were; a later {lit}`ROLLBACK` follows the write that it undoes. -/
def mayChangeRows : Syntax.Statement → Bool
  | .select .. | .begin | .commit | .rollback | .pragma _ => false
  | .insert .. | .insertSelect .. | .update .. | .delete .. | .dropTable .. | .createTable .. | .addColumn ..
  | .createView .. | .createIndex .. | .dropView .. | .dropIndex .. | .createTrigger ..
  | .dropTrigger .. => true

/-- The contexts of the statements of a script that resolves without running, each from the
resolution of the statements before it ({name}`resolveStatement`, as {name}`scriptDiagnostics`
resolves them). The rows are those of the database at the start, until a statement that can
change them ({name}`mayChangeRows`); after it the rows are unknown. The list ends
at the statement that resolves to a restriction, because the model resolves no statement after
it. -/
def resolvedContexts (state : ResolveState) (rows? : Option (List (List Row))) :
    List (Located Syntax.Statement) → List StatementContext
  | [] => []
  | item :: rest =>
    { catalog := state.catalog, rows? } :: match resolveStatement runContext state item.value with
      | .error _ => []
      | .ok (_, next) =>
        resolvedContexts next (if mayChangeRows item.value then none else rows?) rest

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
      { catalog := connection.state.database.catalog, rows? := some connection.state.database.rows }
    match runScriptStep runContext none index connection item.value [] with
    | .ended _ => ([here], [])
    | .continued output next =>
      let later := executedContexts (index + 1) next rest
      (here :: later.1, output :: later.2)

end Belay.Sqlite
