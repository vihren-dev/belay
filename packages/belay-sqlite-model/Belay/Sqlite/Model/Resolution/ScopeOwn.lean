import Belay.Sqlite.Model.Resolution.Scope

set_option doc.verso true

/-! The sources that the {lit}`GROUP BY` and {lit}`ORDER BY` terms of a query can name (ADR 0019, D4; checked
natively with SQLite 3.51.0). -/

namespace Belay.Sqlite.Model

/-- The sources that the {lit}`GROUP BY` and {lit}`ORDER BY` terms of a query can name: its own sources
and the rows of a trigger. SQLite resolves these terms without the columns of the queries around it,
so a term that names one is {lit}`no such column` (checked natively with 3.51.0), while the rows
{lit}`NEW` and {lit}`OLD` of a trigger stay visible. -/
def Scope.ownSources (scope : Scope) : Scope := scope.filter fun source => source.depth == 0 || source.trigger

end Belay.Sqlite.Model
