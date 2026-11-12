import Belay.Sqlite.Model.Programs.Scripts.DropTableStepLaws
import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame
import Belay.Sqlite.Model.Programs.Scripts.CreateTableStepLaws
import Belay.Sqlite.Model.Schema.Columns.SchemaFailureLaws

set_option doc.verso true

/-! The failure laws of CREATE TABLE and DROP TABLE (ADR 0017, S6): a statement that SQLite refuses
(a name that is in use, a table that does not exist) is a prepare error of the model, and a step of
a prepare error leaves the connection as it was. A CREATE TABLE that the model runs never fails, so every
failed step of CREATE TABLE keeps the connection. The same holds for DROP TABLE when foreign keys are off. With
foreign keys on, a drop runs the key run, which can fail during execution; this module has no law for it
(see {lit}`DropTableStepLaws` for the failure law with a premise on the key run). -/

namespace Belay.Sqlite.Model

/-- For every connection and CREATE TABLE statement, and every step that continues with an error output: the
step has no further execution, and the next connection is the connection. In plain words, a CREATE TABLE
that fails changes nothing, not even the counters (failure law), with or without {lit}`IF NOT EXISTS`. Proof
sketch: the statement resolves to a prepare error, to a CREATE TABLE ({name}`resolveCreateTable_form`) or to
the no-op of the clause ({name}`resolveCreateTableIf_cases`); a CREATE TABLE step and a drop without rules
have no error output ({name}`runScriptStep_createTable`, {name}`runScriptStep_drop_plain`), and a prepare
error keeps the connection ({name}`runScriptStep_readOnly_keeps`). -/
theorem runScriptStep_createTable_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {name : Identifier} {columns : List Syntax.ColumnDefinition} {constraints : List Syntax.TableConstraint}
    {options : Syntax.TableOptions} {ifNotExists : Bool} {parameters : List Value} {output : Output}
    {others : List StatementExecution}
    (step : runScriptStep context clock index connection (.createTable name columns constraints options ifNotExists)
      parameters = .continued output next others)
    (failed : output.isError = true) : others = [] ∧ next = connection := by
  obtain ⟨resolved, after, -, found, -⟩ := runScriptStep_continued_spec step
  have form : (∃ error, resolved = .prepareError error) ∨
      (∃ target created table, resolved = .createTable target created table) ∨ resolved = .drop [] := by
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at found
    cases resolution : resolveCreateTableIf context connection.resolveState.catalog name columns constraints options
        ifNotExists with
    | error restriction => simp [resolution] at found
    | ok pair =>
      obtain ⟨statement, catalog⟩ := pair
      rw [resolution] at found
      simp only [Except.ok.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      rcases resolveCreateTableIf_cases resolution with ⟨rfl, -⟩ | creation
      · exact .inr (.inr rfl)
      · rcases resolveCreateTable_form context _ catalog name columns constraints options statement creation with
          error | created
        · exact .inl error
        · exact .inr (.inl created)
  rcases form with ⟨error, rfl⟩ | ⟨target, created, table, rfl⟩ | rfl
  · exact runScriptStep_readOnly_keeps found (.inr ⟨error, rfl⟩) step
  · rw [(runScriptStep_createTable found step).1] at failed
    cases failed
  · rw [(runScriptStep_drop_plain found step).1] at failed
    cases failed

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
