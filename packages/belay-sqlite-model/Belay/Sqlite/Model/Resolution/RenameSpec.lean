import Belay.Sqlite.Model.Resolution.CatalogSpec
import Belay.Sqlite.Model.Resolution.Renames
import Belay.Sqlite.Model.Resolution.StatementCatalog

set_option doc.verso true

/-! The resolution laws of ALTER TABLE RENAME TO and RENAME COLUMN: the catalog change of each is one
{name}`Belay.Sqlite.Model.CatalogStep`, and the catalog after it is the catalog change of its resolved
statement. {lit}`NamesSpec.lean` and {lit}`ResolveStateSpec.lean` use them for every statement. -/

namespace Belay.Sqlite.Model

/-- Every successful RENAME TO resolution keeps the catalog and is a prepare error. Proof sketch: every
branch of the resolver is a prepare error or a restriction, which is not a success. -/
theorem resolveRenameTable_unchanged (catalog after : Catalog) (tableName newName : Identifier)
    (statement : Resolved.Statement) (ok : resolveRenameTable catalog tableName newName = .ok (statement, after)) :
    after = catalog ∧ ∃ error, statement = .prepareError error := by
  unfold resolveRenameTable at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, _, rfl⟩) | (cases ok)

/-- Every successful RENAME COLUMN resolution keeps the catalog and is a prepare error. Proof sketch: as
for RENAME TO. -/
theorem resolveRenameColumn_unchanged (catalog after : Catalog) (tableName column : Identifier)
    (columnToken : String) (statement : Resolved.Statement)
    (ok : resolveRenameColumn catalog tableName column columnToken = .ok (statement, after)) :
    after = catalog ∧ ∃ error, statement = .prepareError error := by
  unfold resolveRenameColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, _, rfl⟩) | (cases ok)

/-- Every successful RENAME TO resolution changes the catalog by one step. Proof sketch: the catalog is
unchanged ({name}`resolveRenameTable_unchanged`). -/
theorem resolveRenameTable_step (catalog after : Catalog) (tableName newName : Identifier)
    (statement : Resolved.Statement) (ok : resolveRenameTable catalog tableName newName = .ok (statement, after)) :
    CatalogStep catalog after := by
  obtain ⟨rfl, _⟩ := resolveRenameTable_unchanged _ _ _ _ _ ok
  exact .same

/-- Every successful RENAME COLUMN resolution changes the catalog by one step. Proof sketch: the catalog
is unchanged ({name}`resolveRenameColumn_unchanged`). -/
theorem resolveRenameColumn_step (catalog after : Catalog) (tableName column : Identifier)
    (columnToken : String) (statement : Resolved.Statement)
    (ok : resolveRenameColumn catalog tableName column columnToken = .ok (statement, after)) :
    CatalogStep catalog after := by
  obtain ⟨rfl, _⟩ := resolveRenameColumn_unchanged _ _ _ _ _ _ ok
  exact .same

/-- Every successful RENAME TO resolution gives the catalog change of its resolved statement, which is
not transaction control. Proof sketch: the statement is a prepare error, which keeps the catalog. -/
theorem resolveRenameTable_applyCatalog (catalog after : Catalog) (tableName newName : Identifier)
    (statement : Resolved.Statement) (ok : resolveRenameTable catalog tableName newName = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  obtain ⟨rfl, _, rfl⟩ := resolveRenameTable_unchanged _ _ _ _ _ ok
  exact ⟨rfl, rfl⟩

/-- Every successful RENAME COLUMN resolution gives the catalog change of its resolved statement, which is
not transaction control. Proof sketch: as for RENAME TO. -/
theorem resolveRenameColumn_applyCatalog (catalog after : Catalog) (tableName column : Identifier)
    (columnToken : String) (statement : Resolved.Statement)
    (ok : resolveRenameColumn catalog tableName column columnToken = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  obtain ⟨rfl, _, rfl⟩ := resolveRenameColumn_unchanged _ _ _ _ _ _ ok
  exact ⟨rfl, rfl⟩

end Belay.Sqlite.Model
