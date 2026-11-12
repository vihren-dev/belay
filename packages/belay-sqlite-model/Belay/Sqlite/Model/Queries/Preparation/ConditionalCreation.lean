import Belay.Sqlite.Model.Queries.Preparation.Definitions

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every condition, catalog, resolution, statement and catalog after it: if the resolution
that is the no-op on the catalog when the condition holds, and the given resolution otherwise,
succeeds with the statement and the catalog after it, then

* the statement is {lit}`.drop []` and the catalog after it is {lit}`catalog.drop []`, or
* the given resolution succeeds with the same statement and catalog.

Proof sketch: split the condition. -/
theorem noOpOr_ok {kept : Bool} {catalog after : Catalog} {resolution : StatementResolution}
    {statement : Resolved.Statement}
    (ok : (if kept then .ok (.drop [], catalog.drop []) else resolution) = .ok (statement, after)) :
    (statement = .drop [] ∧ after = catalog.drop []) ∨ resolution = .ok (statement, after) := by
  split at ok
  · cases ok; exact .inl ⟨rfl, rfl⟩
  · exact .inr ok

end Belay.Sqlite.Model
