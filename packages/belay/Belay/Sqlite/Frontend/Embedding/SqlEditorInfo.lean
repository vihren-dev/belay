import Belay.Sqlite.Frontend.Embedding.SqlTableInfo
import Belay.Sqlite.Frontend.Embedding.SqlStatementContexts
import Belay.Sqlite.Frontend.Embedding.SqlTableOrigins
import Belay.Sqlite.Frontend.Embedding.SqlNameInfo

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Belay.Sqlite.Model

/-- What a caller knows about the database that a script starts on. Use the default value for
a database whose declaration and origins are unknown. -/
structure KnownDatabase where
  /-- The declaration that names the database term, shown in the hover. -/
  owner : Option Name := none
  /-- Where the {lit}`CREATE TABLE` of a table of the database at the start is written, when the
  caller knows it. A caller that knows no origin keeps the default. -/
  origin? : Identifier → Option DeclarationLocation := fun _ => none

end Belay.Sqlite
