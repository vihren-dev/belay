import Belay.Sqlite.Model.Schema.Ddl.CatalogSpec
import Belay.Sqlite.Model.Shared.Resolved.StatementCatalog
import Belay.Sqlite.Model.Queries.Preparation.ViewDefinitions

set_option doc.verso true

/-! CREATE VIEW preserves the resolver's catalog-step and execution-catalog links.
Only a fresh name appends a definition; IF NOT EXISTS can remove no positions. -/

namespace Belay.Sqlite.Model

/-- Every successful CREATE VIEW resolution gives one catalog step: a prepare error
keeps the catalog, IF NOT EXISTS can drop nothing, and creation appends at a fresh
name. Proof sketch: split the parameter, reserved-name and catalog lookup checks. -/
theorem resolveCreateView_step (catalog after : Catalog) (name : Identifier) (ifNotExists : Bool)
    (view : CatalogView) (statement : Resolved.Statement)
    (ok : resolveCreateView catalog name ifNotExists view = .ok (statement, after)) :
    CatalogStep catalog after := by
  unfold resolveCreateView at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .same)
    | (cases ok; exact .remove _)
    | (cases ok; exact .append _ (by assumption))
    | cases ok

end Belay.Sqlite.Model
