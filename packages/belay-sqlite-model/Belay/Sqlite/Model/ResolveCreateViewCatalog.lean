import Belay.Sqlite.Model.CatalogValidDrop
import Belay.Sqlite.Model.Resolution.ViewDefinitionSpec

set_option doc.verso true

/-! CREATE VIEW preserves catalog validity without resolving the stored body.
The existing append law permits missing references and cycles in that body. -/

namespace Belay.Sqlite.Model

/-- For every valid catalog and successful CREATE VIEW resolution, the resulting
catalog is valid under the same limits. A prepare error preserves the input;
IF NOT EXISTS can leave it unchanged; creation appends a fresh, nonreserved name.
Proof sketch: split resolution and apply {name}`Catalog.Valid.createView` to the
only branch that appends an object. -/
theorem resolveCreateView_valid (limits : Limits) (catalog after : Catalog) (name : Identifier)
    (ifNotExists : Bool) (view : CatalogView) (statement : Resolved.Statement)
    (valid : catalog.Valid limits)
    (ok : resolveCreateView catalog name ifNotExists view = .ok (statement, after)) : after.Valid limits := by
  unfold resolveCreateView at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact valid)
    | (cases ok; exact valid.drop (Catalog.DropClosed.nil catalog))
    | (cases ok; exact valid.createView name view (by assumption) (by simpa using ‹¬ reservedName name = true›))
    | cases ok

end Belay.Sqlite.Model
