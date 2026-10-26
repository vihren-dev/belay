import Belay.Sqlite.Model.Resolution.Resolve
import Belay.Sqlite.Model.Resolution.CatalogSpec

set_option doc.verso true

/-! The prepare-error rule ({lit}`lang_createtable.html` R-01232-54838 and the
{lit}`no such table` errors of {lit}`sqlite3LocateTable`): resolution gives a prepare
error that names a catalog object exactly when the named object is missing or the name
is already used. An error names a catalog object when it is not
{lit}`PrepareError.expression`: every other error is an {lit}`ExprError`, which is the
only kind of error that the resolution of expressions and clauses can give. For each
statement, one theorem shows that such an error has its cause, and one shows that the
cause gives the error. -/

namespace Belay.Sqlite.Model

/-- For every CREATE TABLE whose resolution is a prepare error that names a catalog
object, the catalog has an object with the folded name, and the catalog is unchanged. -/
theorem resolveCreateTable_named (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (error : PrepareError) (named : ∀ cause, error ≠ .expression cause)
    (ok : resolveCreateTable context catalog name columns constraints options = .ok (.prepareError error, after)) :
    (catalog.find name).isSome = true ∧ after = catalog := by
  unfold resolveCreateTable at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals (try (cases ok; done))
  all_goals cases ok
  all_goals first
    | exact absurd rfl (named _)
    | exact ⟨.inr ⟨_, rfl⟩, rfl⟩
    | (simp_all; done)

/-- For every CREATE TABLE of a name that SQLite does not reserve: when the catalog
has an object with the folded name, the resolution is a prepare error that names a
catalog object, and the catalog is unchanged. -/
theorem resolveCreateTable_used (context : ResolveContext) (catalog : Catalog)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (notReserved : reservedName name = false) (used : (catalog.find name).isSome = true) :
    ∃ error, (∀ cause, error ≠ .expression cause) ∧
      resolveCreateTable context catalog name columns constraints options = .ok (.prepareError error, catalog) := by
  unfold resolveCreateTable
  simp only [notReserved, Bool.false_and, Bool.false_eq_true, ite_false, prepareError]
  cases found : catalog.find name with
  | none => simp [found] at used
  | some result =>
    obtain ⟨_, object⟩ := result
    have live := Catalog.find_not_trigger _ _ _ _ found
    cases entry : object.entry <;> cases object <;> simp_all [CatalogObject.isTrigger, CatalogEntry.isTrigger]

/-- For every INSERT, with any subqueries and shapes, whose resolution is a prepare error that
names a catalog object:
the error is {lit}`no such table` for the statement's table, and no table has the folded
name, or it is {lit}`cannot modify %s because it is a view`; the catalog is unchanged. Proof sketch: split every branch of the
resolver; the branches after the table lookup give errors that name no catalog
object, by the lemmas on column lists, values and full rows. -/
theorem resolveInsert_named (context : ResolveContext) (catalog after : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (error : PrepareError) (named : ∀ cause, error ≠ .expression cause)
    (ok : resolveInsert context catalog tableName names rows conflicts algorithm returning subqueries shapes =
      .ok (.prepareError error, after)) :
    ((error = .noSuchTable tableName ∧ catalog.findTable tableName = none) ∨ ∃ name, error = .viewModify name) ∧
      after = catalog := by
  unfold resolveInsert resolveInsertTraced at ok
  simp only [traced_drop, prepareError, restrict, issueResolution] at ok
  repeat' split at ok
  all_goals (try (cases ok; done))
  all_goals cases ok
  all_goals first
    | exact absurd rfl (named _)
    | exact ⟨.inr ⟨_, rfl⟩, rfl⟩
    | (simp_all; done)

/-- For every INSERT, with any subqueries and shapes, whose VALUES rows all have the width of
the first row: when no
table or view has the folded name, the resolution is {lit}`no such table`, and the catalog
is unchanged. -/
theorem resolveInsert_missing (context : ResolveContext) (catalog : Catalog)
    (tableName : Identifier) (names : Option (List Identifier)) (rows : List (List Syntax.Expr))
    (conflicts : List Syntax.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query) (shapes : SubqueryShapes)
    (same : ∀ row ∈ rows, row.length = (rows.head?.map List.length).getD 0)
    (missing : catalog.findTable tableName = none)
    (notView : catalog.findView tableName = none) :
    resolveInsert context catalog tableName names rows conflicts algorithm returning subqueries shapes =
      .ok (.prepareError (.noSuchTable tableName), catalog) := by
  have consistent : (rows.any fun row => row.length != (rows.head?.map List.length).getD 0) = false := by
    simpa using same
  unfold resolveInsert resolveInsertTraced
  simp [consistent, missing, notView, prepareError, traced_drop]

end Belay.Sqlite.Model
