import Belay.Sqlite.Resolution.CatalogSpec
import Belay.Sqlite.Resolution.StatementCatalog
import Belay.Sqlite.Resolution.TriggerDefinitions

set_option doc.verso true

/-! The resolution laws of CREATE TRIGGER and DROP TRIGGER (ADR 0018, D5): each changes the
catalog by one {name}`Belay.Sqlite.CatalogStep`, and the catalog after it is the catalog change
of its resolved statement. {lit}`NamesSpec.lean` and {lit}`ResolveStateSpec.lean` use them. -/

namespace Belay.Sqlite

/-- For every successful resolution of CREATE TRIGGER, the catalog changes by one
{name}`CatalogStep`: unchanged after a prepare error, the removal of no positions with
{lit}`IF NOT EXISTS`, else one trigger appended. Proof sketch: split every branch of the
resolver. -/
theorem resolveCreateTrigger_step (catalog after : Catalog) (name : Identifier) (ifNotExists : Bool)
    (trigger : CatalogTrigger) (statement : Resolved.Statement)
    (ok : resolveCreateTrigger catalog name ifNotExists trigger = .ok (statement, after)) :
    CatalogStep catalog after := by
  unfold resolveCreateTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .same)
    | (cases ok; exact .remove _)
    | (cases ok; exact .appendTrigger _ rfl)
    | cases ok

/-- For every successful resolution of DROP TRIGGER, the catalog changes by one
{name}`CatalogStep`: unchanged after a prepare error, else the removal of its positions.
Proof sketch: as for CREATE TRIGGER. -/
theorem resolveDropTrigger_step (catalog after : Catalog) (name : Identifier) (ifExists : Bool)
    (statement : Resolved.Statement) (ok : resolveDropTrigger catalog name ifExists = .ok (statement, after)) :
    CatalogStep catalog after := by
  unfold resolveDropTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact .same) | (cases ok; exact .remove _) | cases ok

/-- For every successful resolution of CREATE TRIGGER, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: every branch returns the input catalog with a prepare
error, a drop of no positions, or the catalog of {name}`Catalog.createTrigger`. -/
theorem resolveCreateTrigger_applyCatalog (catalog after : Catalog) (name : Identifier) (ifNotExists : Bool)
    (trigger : CatalogTrigger) (statement : Resolved.Statement)
    (ok : resolveCreateTrigger catalog name ifNotExists trigger = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveCreateTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of DROP TRIGGER, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for CREATE TRIGGER, with {name}`Catalog.drop`. -/
theorem resolveDropTrigger_applyCatalog (catalog after : Catalog) (name : Identifier) (ifExists : Bool)
    (statement : Resolved.Statement) (ok : resolveDropTrigger catalog name ifExists = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveDropTrigger at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

end Belay.Sqlite
