import Belay.Sqlite.Model.Resolution.DropColumnResolve
import Belay.Sqlite.Model.Resolution.RenameSpec

set_option doc.verso true

/-! The resolution laws of ALTER TABLE DROP COLUMN: a successful resolution is a prepare error that keeps the
catalog, or the drop with the catalog after it, which the model can run and the limits allow.
{lit}`NamesSpec.lean` and {lit}`ResolveStatementFacts.lean` use them for every statement. -/

namespace Belay.Sqlite.Model

/-- What a successful resolution of DROP COLUMN is, for the limits: a prepare error with the catalog unchanged, or
the statement {lean}`Resolved.Statement.dropColumn` of a position and an index whose catalog is the catalog after
the drop ({name}`Catalog.dropColumn`), where the drop is one that {name}`Catalog.droppable` accepts and the catalog
after it is supported under the limits. -/
def DropOutcome (limits : Limits) (catalog after : Catalog) (statement : Resolved.Statement) : Prop :=
  (after = catalog ∧ ∃ error, statement = .prepareError error) ∨
    (∃ position index, statement = .dropColumn position index after ∧ after = catalog.dropColumn position index ∧
      catalog.droppable position index = true ∧ after.supported limits = true)

/-- For every resolution input: a successful {name}`finishDropColumn` is {name}`DropOutcome`. Proof sketch: the
failure of a schema test is a prepare error with the catalog unchanged or a restriction, which is no success; the
other success is guarded by the two tests of the definition. -/
theorem finishDropColumn_outcome (context : ResolveContext) (catalog after : Catalog) (target index : Nat)
    (table : CatalogTable) (declared tableName : Identifier) (statement : Resolved.Statement)
    (ok : finishDropColumn context catalog target index table declared tableName = .ok (statement, after)) :
    DropOutcome context.profile.limits catalog after statement := by
  unfold finishDropColumn at ok
  cases tests : dropColumnTests context catalog target index table declared tableName with
  | error failure =>
    rw [tests] at ok
    cases failure <;> simp [RenameFailure.resolution, prepareError, restrict] at ok
    left
    exact ⟨ok.2.symm, _, ok.1.symm⟩
  | ok value =>
    rw [tests] at ok
    simp only [] at ok
    split at ok
    · rename_i guard
      simp only [Except.ok.injEq, Prod.mk.injEq] at ok
      obtain ⟨rfl, rfl⟩ := ok
      simp only [Bool.and_eq_true] at guard
      exact .inr ⟨target, index, rfl, rfl, guard.1, guard.2⟩
    · simp [restrict] at ok

/-- For every successful DROP COLUMN resolution: {name}`DropOutcome`. Proof sketch: every branch of the resolver is a
prepare error, a restriction, which is not a success, or {name}`finishDropColumn`. -/
theorem resolveDropColumn_outcome (context : ResolveContext) (catalog after : Catalog) (tableName column : Identifier)
    (columnToken : String) (statement : Resolved.Statement)
    (ok : resolveDropColumn context catalog tableName column columnToken = .ok (statement, after)) :
    DropOutcome context.profile.limits catalog after statement := by
  unfold resolveDropColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | exact finishDropColumn_outcome _ _ _ _ _ _ _ _ _ ok
    | (cases ok; exact .inl ⟨rfl, _, rfl⟩)
    | (cases ok)

/-- For every outcome of DROP COLUMN: the catalog change is one step. Proof sketch: a prepare error keeps the
catalog; a drop has unique names, because its catalog is supported ({name}`Catalog.supported_iff`). -/
theorem DropOutcome.step {limits : Limits} {catalog after : Catalog} {statement : Resolved.Statement}
    (outcome : DropOutcome limits catalog after statement) : CatalogStep catalog after := by
  rcases outcome with ⟨rfl, _⟩ | ⟨_, _, _, _, _, supported⟩
  · exact .same
  · exact .rewrite after ((Catalog.supported_iff limits after).mp supported).1

/-- For every outcome of DROP COLUMN: the catalog after it is the catalog change of its statement, which is not
transaction control. Proof sketch: a prepare error and a drop each define it. -/
theorem DropOutcome.applyCatalog {limits : Limits} {catalog after : Catalog} {statement : Resolved.Statement}
    (outcome : DropOutcome limits catalog after statement) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  rcases outcome with ⟨rfl, _, rfl⟩ | ⟨_, _, rfl, _⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- For every outcome of DROP COLUMN and supported catalog before it: the catalog after it is supported. Proof
sketch: a prepare error keeps the catalog, and a drop is supported under the limits by its test. -/
theorem DropOutcome.valid {limits : Limits} {catalog after : Catalog} {statement : Resolved.Statement}
    (outcome : DropOutcome limits catalog after statement) (current : catalog.supported limits = true) :
    after.supported limits = true := by
  rcases outcome with ⟨rfl, _⟩ | ⟨_, _, _, _, _, supported⟩
  · exact current
  · exact supported

end Belay.Sqlite.Model
