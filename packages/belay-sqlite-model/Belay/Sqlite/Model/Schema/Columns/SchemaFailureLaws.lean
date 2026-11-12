import Belay.Sqlite.Model.Schema.Dispatch.ResolveStatementForms
import Belay.Sqlite.Model.Schema.Ddl.DropTableResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every context, catalog, name, definitions, constraints, options and resolved statement that
{name}`resolveCreateTable` gives: the statement is a prepare error, or a CREATE TABLE. In plain words,
a CREATE TABLE is refused or it runs. Proof sketch: every branch of the resolver gives a prepare error or
the CREATE TABLE (the branches that end the run give no statement). -/
theorem resolveCreateTable_form (context : ResolveContext) (catalog after : Catalog)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (statement : Resolved.Statement)
    (ok : resolveCreateTable context catalog name columns constraints options = .ok (statement, after)) :
    (∃ error, statement = .prepareError error) ∨ ∃ target created table, statement = .createTable target created table := by
  unfold resolveCreateTable at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inr ⟨_, _, _, rfl⟩)
    | (cases ok; exact .inl ⟨_, rfl⟩)
    | (cases ok; done)

/-- For every context, state with foreign keys off, DROP TABLE and statement that it resolves to: the statement is a
drop, or a prepare error. Proof sketch: as {name}`resolveStatement_dropTable_off`, with
{name}`resolveDropTable_shape`. -/
theorem resolveStatement_dropTable_off_form (context : ResolveContext) (state after : ResolveState) (name : Identifier)
    (ifExists : Bool) {resolved : Resolved.Statement} (off : state.foreignKeys = false)
    (found : resolveStatement context state (.dropTable name ifExists) = .ok (resolved, after)) :
    (∃ positions, resolved = .drop positions none) ∨ ∃ error, resolved = .prepareError error := by
  simp only [statement_arms] at found
  cases resolution : resolveDropTable state.catalog name ifExists with
  | error restriction =>
    simp [resolution, ResolveState.withWrite, ResolveState.withCatalog, Except.map, bind, Except.bind] at found
  | ok pair =>
    obtain ⟨statement, catalog⟩ := pair
    rcases resolveDropTable_shape resolution with ⟨positions, rules, rfl⟩ | ⟨error, rfl⟩
    · rw [resolution, ResolveState.withWrite_drop_off context state _ _ _ off] at found
      simp only [Except.ok.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      exact .inl ⟨positions, by rw [(resolveDropTable_drop resolution).1]⟩
    · rw [resolution, ResolveState.withWrite_prepareError_off context state _ _ off] at found
      simp only [Except.ok.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      exact .inr ⟨error, rfl⟩

end Belay.Sqlite.Model
