import Belay.Sqlite.Model.Shared.Catalog.Catalog
import Belay.Sqlite.Model.Shared.Syntax.ConflictForm

set_option doc.verso true

/-! The conflict algorithm of each constraint of a write. The catalog gives each key's
and each NOT NULL constraint's own algorithm, and an {lit}`INSERT OR` statement
replaces them. Resolution uses the policy to decide model restrictions, and execution
computes it again from the state's catalog. -/

namespace Belay.Sqlite.Model

/-- Whether the policy gives two keys different algorithms other than REPLACE, whose order
SQLite decides internally (the restriction {lit}`mixed-conflict-algorithms`). -/
def Resolved.ConflictPolicy.mixed (policy : Resolved.ConflictPolicy) : Bool :=
  (policy.keys.filter (· != .replace)).eraseDups.length > 1

/-- Whether a NOT NULL column with a default has REPLACE, which would store the default
(the restriction {lit}`replace-default`). -/
def replacesDefault (table : CatalogTable) (policy : Resolved.ConflictPolicy) : Bool :=
  (table.columns.zip policy.notNull).any fun (column, algorithm) =>
    column.notNull && column.defaultValue.isSome && algorithm == .replace

/-- Whether every algorithm of the policy is ABORT, the behavior of a plain INSERT. -/
def Resolved.ConflictPolicy.aborts (policy : Resolved.ConflictPolicy) : Bool :=
  policy.keys.all (· == .abort) && policy.notNull.all (· == .abort) && policy.check == .abort

end Belay.Sqlite.Model
