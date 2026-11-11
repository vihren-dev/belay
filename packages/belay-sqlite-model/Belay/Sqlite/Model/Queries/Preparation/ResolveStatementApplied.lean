import Belay.Sqlite.Model.Shared.Resolved.StatementCatalog

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every statement that is transaction control or a setting ({name}`Resolved.Statement.isControl`) and
every catalog, {name}`Resolved.Statement.applyCatalog` gives the catalog. Proof sketch: a case for each
control statement; the others contradict the premise. -/
theorem Resolved.Statement.applyCatalog_of_control {statement : Resolved.Statement}
    (control : statement.isControl = true) (catalog : Catalog) : statement.applyCatalog catalog = catalog := by
  cases statement <;> first | rfl | cases control

end Belay.Sqlite.Model
