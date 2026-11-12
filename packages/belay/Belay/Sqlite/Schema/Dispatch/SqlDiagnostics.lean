import Belay.Sqlite.Schema.Dispatch.Run
import Belay.Sqlite.Model.Queries.Preparation.Resolution
import Belay.Sqlite.Model.Schema.Triggers.ResolveStatementSingle
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateQuery
import Belay.Sqlite.Queries.Preparation.SqlDiagnostics

set_option doc.verso true

/-! The errors that {lit}`sql! db r"..."` shows in the SQL text, as byte ranges of the text, so
that the elaborator only maps each range into the Lean file. A model restriction has a node path
and shows at the node that the path selects. A prepare error has only the names of its message,
so it shows at the one place of the statement's text that writes that name, or at the statement
when the text writes the name at no place or at more than one place. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- The errors of the statements, resolved in order from the state with the surface's context
({name}`resolveStatement`, {name}`runContext`), step for step as {name}`resolveFrom` resolves
them: each prepare error, and the first model restriction. Resolution stops at the restriction,
so the statements after it show no error. For example, the text {lit}`SELECT nmae FROM t`
against a catalog with the table {lit}`t(a)` gives {lit}`no such column: nmae` at the bytes
from 7 to 11. -/
def scriptDiagnostics (state : ResolveState) (bytes : ByteArray) :
    List (Located Syntax.Statement) → List Diagnostic
  | [] => []
  | item :: rest => match resolveStatement runContext state item.value with
    | .error restriction => [restrictionDiagnostic item restriction]
    | .ok (resolved, next) =>
      (resolved.prepareError?.map (prepareDiagnostic bytes item)).toList ++
        scriptDiagnostics next bytes rest

end Belay.Sqlite
