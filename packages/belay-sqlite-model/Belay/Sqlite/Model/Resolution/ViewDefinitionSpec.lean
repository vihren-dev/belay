import Belay.Sqlite.Model.Resolution.CatalogSpec
import Belay.Sqlite.Model.Resolution.StatementCatalog
import Belay.Sqlite.Model.Resolution.ViewDefinitions

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

/-- Every successful CREATE VIEW resolution leaves exactly the catalog that its
resolved statement applies, and the statement is not transaction control.
Proof sketch: every branch is a prepare error, empty drop or fresh view append. -/
theorem resolveCreateView_applyCatalog (catalog after : Catalog) (name : Identifier) (ifNotExists : Bool)
    (view : CatalogView) (statement : Resolved.Statement)
    (ok : resolveCreateView catalog name ifNotExists view = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveCreateView at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | cases ok

end Belay.Sqlite.Model
