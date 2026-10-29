import Belay.Sqlite.Model.Resolution.CatalogSpec
import Belay.Sqlite.Model.Resolution.Renames
import Belay.Sqlite.Model.Resolution.StatementCatalog
import Belay.Sqlite.Model.Resolution.SupportedNames

set_option doc.verso true

/-! The resolution laws of ALTER TABLE RENAME TO and RENAME COLUMN: a successful resolution is a prepare error
that keeps the catalog, or the rewrite of the catalog by {lit}`renameCatalog`, whose catalog is supported. The
catalog change of each is one {name}`Belay.Sqlite.Model.CatalogStep`, and the catalog after it is the catalog
change of its resolved statement. {lit}`NamesSpec.lean` and {lit}`ResolveStatementFacts.lean` use them for every
statement. -/

namespace Belay.Sqlite.Model

/-- What a successful resolution of a rename is, for the limits: a prepare error with the catalog unchanged, or
the rewrite with the new catalog, which is supported under the limits. -/
def RenameOutcome (limits : Limits) (catalog after : Catalog) (statement : Resolved.Statement) : Prop :=
  (after = catalog ∧ ∃ error, statement = .prepareError error) ∨
    (statement = .rewrite after ∧ after.supported limits = true)

/-- For every context, catalog, request and names: if {name}`renameCatalog` gives a catalog, the catalog is
supported under the limits of the profile. Proof sketch: the last test of the function is the test of
{name}`Catalog.supported`, and its other steps give the catalog only when the test passes. -/
theorem renameCatalog_supported (context : ResolveContext) (catalog renamed : Catalog) (request : RenameRequest)
    (oldTable oldColumn : Identifier) (ok : renameCatalog context catalog request oldTable oldColumn = .ok renamed) :
    renamed.supported context.profile.limits = true := by
  unfold renameCatalog at ok
  cases first : catalog.zipIdx.mapM fun (object, position) =>
      renameObject context catalog request oldTable oldColumn position object with
  | error failure => simp [first, bind, Except.bind] at ok
  | ok stored =>
    cases second : stored.zipIdx.forM fun (object, position) => checkRenamedObject context stored position object with
    | error failure => simp [first, second, bind, Except.bind] at ok
    | ok _ =>
      simp only [first, second, bind, Except.bind] at ok
      split at ok
      · cases ok; assumption
      · cases ok

/-- For every context, catalog, request and names: a successful {name}`finishRename` is a prepare error that
keeps the catalog, or a rewrite with a supported catalog. Proof sketch: the failure of the rewrite is a
prepare error with the catalog unchanged or a restriction, which is no success; its success is
{name}`renameCatalog_supported`. -/
theorem finishRename_outcome (context : ResolveContext) (catalog after : Catalog) (request : RenameRequest)
    (oldTable oldColumn : Identifier) (statement : Resolved.Statement)
    (ok : finishRename context catalog request oldTable oldColumn = .ok (statement, after)) :
    RenameOutcome context.profile.limits catalog after statement := by
  unfold finishRename at ok
  cases renamed : renameCatalog context catalog request oldTable oldColumn with
  | error failure =>
    rw [renamed] at ok
    cases failure <;> simp [RenameFailure.resolution, prepareError, restrict] at ok
    left
    exact ⟨ok.2.symm, _, ok.1.symm⟩
  | ok value =>
    rw [renamed] at ok
    simp only [Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    exact .inr ⟨rfl, renameCatalog_supported context catalog _ request oldTable oldColumn renamed⟩

/-- For every successful RENAME TO resolution: {name}`RenameOutcome`. Proof sketch: every branch of the
resolver is a prepare error, a restriction, which is not a success, or {name}`finishRename`. -/
theorem resolveRenameTable_outcome (context : ResolveContext) (catalog after : Catalog) (tableName newName : Identifier)
    (statement : Resolved.Statement)
    (ok : resolveRenameTable context catalog tableName newName = .ok (statement, after)) :
    RenameOutcome context.profile.limits catalog after statement := by
  unfold resolveRenameTable at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | exact finishRename_outcome _ _ _ _ _ _ _ ok
    | (cases ok; exact .inl ⟨rfl, _, rfl⟩)
    | (cases ok)

/-- For every successful RENAME COLUMN resolution: {name}`RenameOutcome`. Proof sketch: as for RENAME TO. -/
theorem resolveRenameColumn_outcome (context : ResolveContext) (catalog after : Catalog)
    (tableName column newName : Identifier) (columnToken : String) (quoted : Bool) (statement : Resolved.Statement)
    (ok : resolveRenameColumn context catalog tableName column newName columnToken quoted = .ok (statement, after)) :
    RenameOutcome context.profile.limits catalog after statement := by
  unfold resolveRenameColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | exact finishRename_outcome _ _ _ _ _ _ _ ok
    | (cases ok; exact .inl ⟨rfl, _, rfl⟩)
    | (cases ok)

/-- For every outcome of a rename: the catalog change is one step. Proof sketch: a prepare error keeps the
catalog; a rewrite has unique names, because its catalog is supported ({name}`Catalog.supported_iff`). -/
theorem RenameOutcome.step {limits : Limits} {catalog after : Catalog} {statement : Resolved.Statement}
    (outcome : RenameOutcome limits catalog after statement) : CatalogStep catalog after := by
  rcases outcome with ⟨rfl, _⟩ | ⟨_, supported⟩
  · exact .same
  · exact .rewrite after ((Catalog.supported_iff limits after).mp supported).1

/-- For every outcome of a rename: the catalog after it is the catalog change of its statement, which is
not transaction control. Proof sketch: a prepare error and a rewrite each define it. -/
theorem RenameOutcome.applyCatalog {limits : Limits} {catalog after : Catalog} {statement : Resolved.Statement}
    (outcome : RenameOutcome limits catalog after statement) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  rcases outcome with ⟨rfl, _, rfl⟩ | ⟨rfl, _⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- For every outcome of a rename and valid catalog before it: the catalog after it is valid. Proof sketch: a
prepare error keeps the catalog, and a rewrite is supported under the limits by its test. -/
theorem RenameOutcome.valid {limits : Limits} {catalog after : Catalog} {statement : Resolved.Statement}
    (outcome : RenameOutcome limits catalog after statement) (current : catalog.supported limits = true) :
    after.supported limits = true := by
  rcases outcome with ⟨rfl, _⟩ | ⟨_, supported⟩
  · exact current
  · exact supported

end Belay.Sqlite.Model
