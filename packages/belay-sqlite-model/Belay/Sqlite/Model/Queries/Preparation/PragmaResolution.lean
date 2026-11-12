import Belay.Sqlite.Model.Shared.Resolved.ResolveState
import Belay.Sqlite.Model.Queries.Preparation.PragmaRows

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The query of the rows of a pragma with the names of its columns: each result column is
the cell at its position, and the query has no condition, order or window. -/
def pragmaQuery (rows : Resolved.PragmaRows) (names : List String) : Resolved.Query :=
  { sources := [{ kind := .inner, source := .pragma rows, condition := none }], filter := none,
    aggregate := false, groupBy := [], columns := (List.range names.length).map fun position => .scalar (.column position),
    names, orderBy := [], offset := 0, limit := none }

/-- The query of a setting: one row with the column of its name ({name}`Syntax.PragmaSetting.sqlName`),
1 when the setting is on and 0 when it is off. -/
def settingQuery (setting : Syntax.PragmaSetting) (on : Bool) : Resolved.Statement :=
  .query (pragmaQuery (.fixed 1 [[.integer (if on then 1 else 0)]]) [setting.sqlName]) []

/-- The query of a check pragma with the limit, for the table at the catalog position or for
every table: one column with the name of the pragma ({name}`Syntax.checkName`). -/
def checkQuery (quick : Bool) (limit : Nat) (table : Option Nat) : Resolved.Statement :=
  .query (pragmaQuery (.check quick limit table) [Syntax.checkName quick]) []

end Belay.Sqlite.Model
