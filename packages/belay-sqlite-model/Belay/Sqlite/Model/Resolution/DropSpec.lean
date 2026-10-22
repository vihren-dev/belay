import Belay.Sqlite.Model.Resolution.CatalogSpec
import Belay.Sqlite.Model.Resolution.StatementCatalog

set_option doc.verso true

/-! The resolution laws of DROP TABLE and DROP INDEX (ADR 0014, D7): each changes the catalog
by one {name}`Belay.Sqlite.Model.CatalogStep`, and the catalog after it is the catalog change of its resolved
statement. {lit}`NamesSpec.lean` and {lit}`ResolveStateSpec.lean` use them for every
statement. -/

namespace Belay.Sqlite.Model

/-- For every successful resolution of DROP TABLE, the catalog changes by one
{name}`CatalogStep`: unchanged after a prepare error, else the removal of its positions.
Proof sketch: split every branch of the resolver; a prepare error returns the catalog
({name}`CatalogStep.same`), and every other branch returns {name}`Catalog.drop` of the
positions of its statement ({name}`CatalogStep.remove`). -/
theorem resolveDropTable_step (catalog after : Catalog) (name : Identifier) (ifExists : Bool)
    (statement : Resolved.Statement) (ok : resolveDropTable catalog name ifExists = .ok (statement, after)) :
    CatalogStep catalog after := by
  unfold resolveDropTable at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact .same) | (cases ok; exact .remove _) | cases ok

/-- For every successful resolution of DROP INDEX, the catalog changes by one
{name}`CatalogStep`: unchanged after a prepare error, else the removal of its positions.
Proof sketch: as for DROP TABLE; the restriction branch has no resolution. -/
theorem resolveDropIndex_step (catalog after : Catalog) (name : Identifier) (ifExists : Bool)
    (statement : Resolved.Statement) (ok : resolveDropIndex catalog name ifExists = .ok (statement, after)) :
    CatalogStep catalog after := by
  unfold resolveDropIndex at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact .same) | (cases ok; exact .remove _) | cases ok

/-- For every successful resolution of DROP TABLE, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: every branch returns the input catalog with a prepare
error, or a drop with {name}`Catalog.drop` of its positions. -/
theorem resolveDropTable_applyCatalog (catalog after : Catalog) (name : Identifier) (ifExists : Bool)
    (statement : Resolved.Statement) (ok : resolveDropTable catalog name ifExists = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveDropTable at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of DROP INDEX, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for DROP TABLE. -/
theorem resolveDropIndex_applyCatalog (catalog after : Catalog) (name : Identifier)
    (ifExists : Bool) (statement : Resolved.Statement)
    (ok : resolveDropIndex catalog name ifExists = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveDropIndex at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

end Belay.Sqlite.Model
