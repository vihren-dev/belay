import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.ForeignKeyExamples

open Belay.Sqlite.Model

#guard (PrepareError.foreignKeyMismatch (name! "c") (name! "p")).message == "foreign key mismatch - \"c\" referencing \"p\""

#guard (PrepareError.noSuchReferencedTable (name! "q")).message == "no such table: main.q"

end Belay.Sqlite.Model.ForeignKeyExamples
