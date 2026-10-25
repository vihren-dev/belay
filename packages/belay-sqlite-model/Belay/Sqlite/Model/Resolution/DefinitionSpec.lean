import Belay.Sqlite.Model.Resolution.Resolve
import Belay.Sqlite.Model.Resolution.CatalogSpec

set_option doc.verso true

/-! The prepare-error rule for ADD COLUMN and CREATE INDEX, and the transaction rule.
See {lit}`PrepareSpec.lean` for the prepare-error rule. -/

namespace Belay.Sqlite.Model

/-- For every ADD COLUMN whose resolution is a prepare error that names a catalog
object: the error is {lit}`no such table` for the statement's table and no table has the
folded name, or it is {lit}`Cannot add a column to a view`; the catalog is unchanged.
It holds for either value of {lit}`enforced`, which sets only the refusal field of an ADD COLUMN statement. -/
theorem resolveAddColumn_named (context : ResolveContext) (enforced : Bool) (catalog after : Catalog)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition) (error : PrepareError)
    (named : ∀ cause, error ≠ .expression cause)
    (ok : resolveAddColumn context catalog enforced tableName definition = .ok (.prepareError error, after)) :
    ((error = .noSuchTable tableName ∧ catalog.findTable tableName = none) ∨ error = .viewAddColumn) ∧
      after = catalog := by
  unfold resolveAddColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals (try (cases ok; done))
  all_goals cases ok
  all_goals first
    | exact absurd rfl (named _)
    | exact ⟨.inr rfl, rfl⟩
    | (simp_all; done)

/-- For every ADD COLUMN: when no table or view has the folded name, the resolution is
{lit}`no such table`, and the catalog is unchanged.
It holds for either value of {lit}`enforced`, which sets only the refusal field of an ADD COLUMN statement. -/
theorem resolveAddColumn_missing (context : ResolveContext) (enforced : Bool) (catalog : Catalog)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (missing : catalog.findTable tableName = none)
    (notView : catalog.findView tableName = none) :
    resolveAddColumn context catalog enforced tableName definition =
      .ok (.prepareError (.noSuchTable tableName), catalog) := by
  unfold resolveAddColumn
  simp [missing, notView, prepareError]

/-- For every column name, constraint list and error: when the first parse error of the
constraints ({name}`Syntax.ColumnConstraint.parseError`) is the error, it is no
{name}`ExprError.duplicateColumn`. Proof sketch: induction over the constraints; the first
constraint with a parse error gives the error, and a case analysis on that constraint
shows that a parse error is {lit}`no such collation sequence` or the foreign-key error,
never a duplicate column. -/
theorem findSome_parseError_ne_duplicate (column name : Identifier) (constraints : List Syntax.ColumnConstraint)
    (error : ExprError) (found : constraints.findSome? (·.parseError column) = some error) :
    error ≠ .duplicateColumn name := by
  induction constraints with
  | nil => simp at found
  | cons constraint rest ih =>
    rw [List.findSome?_cons] at found
    cases parsed : constraint.parseError column with
    | none => rw [parsed] at found; exact ih found
    | some first =>
      rw [parsed] at found
      cases found
      cases constraint <;> simp only [Syntax.ColumnConstraint.parseError] at parsed <;>
        (repeat' split at parsed) <;> (try cases parsed) <;> simp

/-- The duplicate-column rule of ADD COLUMN ({lit}`sqlite3AddColumn`): for every
table that the folded name finds, whose name SQLite does not reserve and with fewer
columns than the profile limit, the resolution is {lit}`duplicate column name` exactly
when a column of the table has the folded name of the new column.
It holds for either value of {lit}`enforced`, which sets only the refusal field of an ADD COLUMN statement. -/
theorem resolveAddColumn_duplicate (context : ResolveContext) (enforced : Bool) (catalog : Catalog)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable tableName = some (position, table))
    (notReserved : reservedName tableName = false)
    (room : table.columns.length + 1 ≤ context.profile.limits.columns) :
    resolveAddColumn context catalog enforced tableName definition =
        .ok (.prepareError (.expression (.duplicateColumn definition.name)), catalog) ↔
      (columnPosition table.columns definition.name).isSome = true := by
  unfold resolveAddColumn
  have room' : ¬ table.columns.length + 1 > context.profile.limits.columns := by omega
  simp only [found, notReserved, Bool.false_eq_true, ite_false, room', prepareError]
  by_cases used : (columnPosition table.columns definition.name).isSome = true
  · simp [used]
  · simp only [used]
    repeat' split
    all_goals (try simp_all [restrict])
    all_goals exact findSome_parseError_ne_duplicate _ _ _ _ (by assumption)

/-- For every CREATE INDEX whose resolution is a prepare error
that names a catalog object: either no table has the folded table name and the error
is {lit}`no such table`, or an object has the folded index name, or the error is
{lit}`views may not be indexed` ({name}`PrepareError.viewNotIndexed`); and the catalog is
unchanged. -/
theorem resolveCreateIndex_named (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr)
    (error : PrepareError) (named : ∀ cause, error ≠ .expression cause)
    (ok : resolveCreateIndex context catalog name unique tableName terms filter = .ok (.prepareError error, after)) :
    ((catalog.findTable tableName = none ∧ error = .noSuchTable tableName) ∨
      (catalog.find name).isSome = true ∨ error = .viewNotIndexed) ∧ after = catalog := by
  unfold resolveCreateIndex at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals (try (cases ok; done))
  all_goals cases ok
  all_goals first
    | exact absurd rfl (named _)
    | exact ⟨.inr (.inr rfl), rfl⟩
    | (simp_all; done)

/-- For every CREATE INDEX: when no table or view has the folded table name, the resolution is
{lit}`no such table`, and the catalog is unchanged. -/
theorem resolveCreateIndex_missing (context : ResolveContext) (catalog : Catalog)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr)
    (missing : catalog.findTable tableName = none)
    (notView : catalog.findView tableName = none) :
    resolveCreateIndex context catalog name unique tableName terms filter =
      .ok (.prepareError (.noSuchTable tableName), catalog) := by
  unfold resolveCreateIndex
  simp [missing, notView, prepareError]

/-- For every CREATE INDEX on a table that the folded name
finds, where SQLite reserves neither name: when an object has the folded index name,
the resolution is a prepare error that names a catalog object. -/
theorem resolveCreateIndex_used (context : ResolveContext) (catalog : Catalog)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr)
    (position : Nat) (table : CatalogTable) (found : catalog.findTable tableName = some (position, table))
    (tableAllowed : reservedName tableName = false) (nameAllowed : reservedName name = false)
    (used : (catalog.find name).isSome = true) :
    ∃ error, (∀ cause, error ≠ .expression cause) ∧
      resolveCreateIndex context catalog name unique tableName terms filter = .ok (.prepareError error, catalog) := by
  unfold resolveCreateIndex
  simp only [found, tableAllowed, nameAllowed, Bool.false_eq_true, ite_false, prepareError]
  cases hfind : catalog.find name with
  | none => simp [hfind] at used
  | some result =>
    obtain ⟨_, object⟩ := result
    have live := Catalog.find_not_trigger _ _ _ _ hfind
    cases object with
    | mk objectName entry => cases entry <;> simp_all [CatalogObject.isTrigger, CatalogEntry.isTrigger]

end Belay.Sqlite.Model
