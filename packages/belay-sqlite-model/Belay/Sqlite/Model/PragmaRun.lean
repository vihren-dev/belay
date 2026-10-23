import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.Resolution.PragmaSource

set_option doc.verso true

/-! The rows of a pragma over a database (ADR 0019, D2): the rows that a query over the
source {lit}`Resolved.Source.pragma` reads. -/

namespace Belay.Sqlite.Model.Resolved

/-- The rows of the pragma over the database, or {lean}`(none : Option (List (List Value)))`
when the model does not give them. The fixed rows of resolution do not read the database. -/
def PragmaRows.rowsOn (_database : Database) : PragmaRows → Option (List (List Value))
  | .fixed _ rows => some rows

end Belay.Sqlite.Model.Resolved
