import Belay.Sqlite.Model.Queries.Preparation.CatalogSpec
import Belay.Sqlite.Model.Shared.Resolved.StatementCatalog
import Belay.Sqlite.Model.Queries.Preparation.ViewDefinitions

set_option doc.verso true

namespace Belay.Sqlite.Model

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
