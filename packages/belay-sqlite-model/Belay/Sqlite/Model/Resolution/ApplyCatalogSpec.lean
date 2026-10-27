import Belay.Sqlite.Model.Resolution.WriteCatalogSpec
import Belay.Sqlite.Model.Resolution.StatementCatalog

set_option doc.verso true

/-! The catalog after the resolution of CREATE TABLE, CREATE INDEX and ALTER TABLE ADD COLUMN: it is the
catalog function of the resolved statement ({name}`Belay.Sqlite.Model.Resolved.Statement.applyCatalog`),
which is not transaction control. {lit}`ResolveStateSpec.lean` uses these laws for the state after every
statement. -/

namespace Belay.Sqlite.Model

/-- For every successful resolution of CREATE TABLE, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: every branch returns the input catalog with a prepare
error, or the CREATE TABLE at the end of the catalog with {name}`Catalog.createTable`. -/
theorem resolveCreateTable_applyCatalog (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (statement : Resolved.Statement)
    (ok : resolveCreateTable context catalog name columns constraints options = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveCreateTable at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of CREATE INDEX, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for CREATE TABLE, with {name}`Catalog.createIndex`.
-/
theorem resolveCreateIndex_applyCatalog (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr)
    (statement : Resolved.Statement)
    (ok : resolveCreateIndex context catalog name unique tableName terms filter = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveCreateIndex at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of ADD COLUMN, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for CREATE TABLE, with {name}`Catalog.addColumn`.
It holds for either value of {lit}`enforced`, which sets only the refusal field of an ADD COLUMN statement. -/
theorem resolveAddColumn_applyCatalog (context : ResolveContext) (enforced : Bool) (catalog after : Catalog)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition) (statement : Resolved.Statement)
    (ok : resolveAddColumn context catalog enforced tableName definition = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveAddColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

end Belay.Sqlite.Model
