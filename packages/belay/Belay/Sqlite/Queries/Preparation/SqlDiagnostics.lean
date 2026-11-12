import Belay.Sqlite.Model.Queries.Preparation.ErrorNames
import Belay.Sqlite.Frontend.Embedding.SqlDiagnostics

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- The prepare error at the name of its message in the statement ({name}`PrepareError.name?`,
{name}`nameRange?`), or at the statement; the message is SQLite's
({name}`PrepareError.message`). -/
def prepareDiagnostic (bytes : ByteArray) (item : Located Syntax.Statement) (error : PrepareError) :
    Diagnostic :=
  let (start, stop) := (error.name?.bind (nameRange? bytes item.span)).getD (statementRange item)
  { start, stop, message := error.message }

/-- The restriction at the node that its path selects in the statement ({name}`Span.select`),
with the model's reason ({name}`NodeRestriction.reason`): SQLite runs such SQL, so it gives no
message. -/
def restrictionDiagnostic (item : Located Syntax.Statement) (restriction : NodeRestriction) :
    Diagnostic :=
  let (start, stop) := item.span.select restriction.path
  { start, stop, message := restriction.reason }

end Belay.Sqlite
