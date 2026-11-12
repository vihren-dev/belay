import Belay.Sqlite.Frontend.Embedding.SqlDiagnostics
import Belay.Sqlite.Model

set_option doc.verso true

namespace Belay.Sqlite

/-- The message of a statement that has more than one possible execution in the model. A {lit}`db!` text
builds one database, so the statement must have one execution. -/
def ambiguousMessage : String :=
  "the model gives this statement more than one possible result, and db! builds one database; " ++
    "change the statement so that its result is the same in every case, or remove it"

end Belay.Sqlite
