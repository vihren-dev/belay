import Belay.Sqlite.Model.Shared.Catalog.Catalog
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyAction

set_option doc.verso true

/-! The rows of {lit}`PRAGMA table_info` and {lit}`PRAGMA foreign_key_list` (ADR 0019, D2), which
read only the catalog, as SQLite's {lit}`pragma.c` gives them. Resolution computes them, because
each statement resolves against the catalog of its own time. -/

namespace Belay.Sqlite.Model

/-- The names of the columns of {lit}`PRAGMA foreign_key_check`. -/
def foreignKeyCheckNames : List String := ["table", "rowid", "parent", "fkid"]

end Belay.Sqlite.Model
