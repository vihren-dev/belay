import Belay.Sqlite.Model.Resolution.StatementArms
import Belay.Sqlite.Model.DropTableStepLaws
import Belay.Sqlite.Model.ReadOnlyFrame
import Belay.Sqlite.Model.ResolveStatementForms

set_option doc.verso true

/-! The failure laws of CREATE TABLE and DROP TABLE (ADR 0017, S6): a statement that SQLite refuses
(a name that is in use, a table that does not exist) is a prepare error of the model, and a step of
a prepare error leaves the connection as it was. A CREATE TABLE that the model runs never fails, so every
failed step of CREATE TABLE keeps the connection. The same holds for DROP TABLE when foreign keys are off. With
foreign keys on, a drop runs the key run, which can fail during execution; this module has no law for it
(see {lit}`DropTableStepLaws` for the failure law with a premise on the key run). -/

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

/-- For every connection and CREATE TABLE statement, and every step that continues with an error output: the
step has no further execution, and the next connection is the connection. In plain words, a CREATE TABLE
that fails changes nothing, not even the counters (failure law). Proof sketch: the statement resolves to a
prepare error or to a CREATE TABLE ({name}`resolveCreateTable_form`); a CREATE TABLE step has no error
output ({name}`runScriptStep_createTable`), and a prepare error keeps the connection
({name}`runScriptStep_readOnly_keeps`). -/
theorem runScriptStep_createTable_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {name : Identifier} {columns : List Syntax.ColumnDefinition} {constraints : List Syntax.TableConstraint}
    {options : Syntax.TableOptions} {parameters : List Value} {output : Output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection (.createTable name columns constraints options) parameters =
      .continued output next others)
    (failed : output.isError = true) : others = [] ∧ next = connection := by
  obtain ⟨resolved, after, -, found, -⟩ := runScriptStep_continued_spec step
  have form : (∃ error, resolved = .prepareError error) ∨ ∃ target created table, resolved = .createTable target created table := by
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at found
    cases resolution : resolveCreateTable context connection.resolveState.catalog name columns constraints options with
    | error restriction => simp [resolution] at found
    | ok pair =>
      obtain ⟨statement, catalog⟩ := pair
      rw [resolution] at found
      simp only [Except.ok.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      exact resolveCreateTable_form context _ catalog name columns constraints options statement resolution
  rcases form with ⟨error, rfl⟩ | ⟨target, created, table, rfl⟩
  · exact runScriptStep_readOnly_keeps found (.inr ⟨error, rfl⟩) step
  · rw [(runScriptStep_createTable found step).1] at failed
    cases failed

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

/-- For every connection with foreign keys off and DROP TABLE statement, and every step that continues with an
error output: the step has no further execution, and the next connection is the connection. In plain words, with
foreign keys off a DROP TABLE that fails (the table does not exist, or it is a schema table) changes nothing, not
even the counters (failure law). Proof sketch: the statement resolves to a drop without rules or a prepare error
({name}`resolveStatement_dropTable_off_form`); a plain drop step has no error output
({name}`runScriptStep_drop_plain`), and a prepare error keeps the connection
({name}`runScriptStep_readOnly_keeps`). -/
theorem runScriptStep_dropTable_off_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {dropped : Identifier} {ifExists : Bool} {parameters : List Value} {output : Output}
    {others : List StatementExecution} (off : connection.foreignKeys = false)
    (step : runScriptStep context clock index connection (.dropTable dropped ifExists) parameters =
      .continued output next others)
    (failed : output.isError = true) : others = [] ∧ next = connection := by
  obtain ⟨resolved, after, -, found, -⟩ := runScriptStep_continued_spec step
  rcases resolveStatement_dropTable_off_form context _ after dropped ifExists off found with
    ⟨positions, rfl⟩ | ⟨error, rfl⟩
  · rw [(runScriptStep_drop_plain found step).1] at failed
    cases failed
  · exact runScriptStep_readOnly_keeps found (.inr ⟨error, rfl⟩) step

end Belay.Sqlite.Model
