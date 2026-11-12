import Belay.Sqlite.Schema.Rows.DbDiagnostics
import Belay.Sqlite.Frontend.Embedding.SqlStatementContexts

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- Whether the statement can change the stored rows of a table, or the catalog positions that
index them, so that rows known before it are not known after it. Every statement that writes, and
every statement that creates, drops or alters a catalog object, counts: a dropped view or index
moves the positions of the objects after it. Only a query, a transaction statement and a pragma
leave the rows as they were; a later {lit}`ROLLBACK` follows the write that it undoes. -/
def mayChangeRows : Syntax.Statement → Bool
  | .select .. | .begin | .commit | .rollback | .pragma _ => false
  | .insert .. | .insertSelect .. | .update .. | .delete .. | .dropTable .. | .createTable .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn ..
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
    { state, rows? } :: match resolveStatement runContext state item.value with
      | .error _ => []
      | .ok (_, next) =>
        resolvedContexts next (if mayChangeRows item.value then none else rows?) rest

end Belay.Sqlite
