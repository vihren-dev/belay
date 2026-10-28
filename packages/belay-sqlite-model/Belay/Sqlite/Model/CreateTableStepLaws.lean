import Belay.Sqlite.Model.OrdinaryStepEffects
import Belay.Sqlite.Model.TableByName

set_option doc.verso true

/-! The step laws of CREATE TABLE (ADR 0017, S6): what one step of a resolved CREATE TABLE does to the
connection. They are the failure, success and frame laws of the statement at the level of
{lit}`runScriptStep`. -/

namespace Belay.Sqlite.Model

/-- For every connection and statement that resolves to a CREATE TABLE, and every step that continues:
the step has no error output and no further execution, the new table is appended at the end of the
catalog, with an empty row list, and the next connection is the connection with that database and
nothing else changed. In plain words, this is the failure law (CREATE TABLE never continues with an
error: when the model does not describe it on the database, the run ends and the connection stays as it
is) and the success law (the database after is the catalog with the table appended and one empty row
list appended to the rows, a function of the database before). The conclusions also say that the target
position of the resolution is the end of the catalog and that the rows are aligned with the catalog.
Proof sketch: the only error of the effect is {name}`ExecutionError.unmodeled`
({name}`runScriptStep_effect_of_unmodeled`), so the effect succeeds, which holds exactly when the guard
of {name}`step` holds; the run counts nothing ({name}`Counters.apply_default`). -/
theorem runScriptStep_createTable {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {target : Nat} {name : Identifier} {table : CatalogTable}
    (found : resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      target = connection.state.database.catalog.length ∧
      connection.state.database.rows.length = connection.state.database.catalog.length ∧
      next = { connection with state := { connection.state with database :=
        { catalog := connection.state.database.catalog.createTable name table,
          rows := connection.state.database.rows ++ [[]] } } } := by
  have unmodeled : ∀ value reason reached,
      (connection.state.statementRun value parameters (.createTable target name table)).effect =
        .error (reason, reached) → reason = .unmodeled := by
    intro value reason reached effect
    simp only [SqlState.statementRun, runStatement, Model.step] at effect
    split at effect <;> simp_all
  obtain ⟨noError, value, database, -, effect, nextEq⟩ := runScriptStep_effect_of_unmodeled found rfl
    (by intro _ _ same; cases same) step unmodeled
  simp only [SqlState.statementRun, runStatement, Model.step] at effect
  split at effect
  · rename_i guard
    cases effect
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    refine ⟨noError, runScriptStep_others step found rfl, guard.1, guard.2, ?_⟩
    rw [nextEq]
    simp [SqlState.statementRun, runStatement]
  · cases effect

/-- For every connection, statement that resolves to a CREATE TABLE and step that continues, and every
name that finds a table in the database of the connection: the name finds the same table, with the
same rows, at the same position in the database of the next connection. In plain words, CREATE TABLE
keeps every table that it does not create, found by name. Proof sketch:
{name}`runScriptStep_createTable` gives the next database, and {name}`Database.tableNamed_createTable`
the lookup. -/
theorem runScriptStep_createTable_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {target : Nat} {created : Identifier} {definition : CatalogTable}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.createTable target created definition, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    {name : Identifier} {position : Nat} {table : Table}
    (present : connection.state.database.tableNamed name = some (position, table)) :
    next.state.database.tableNamed name = some (position, table) := by
  obtain ⟨-, -, -, -, nextEq⟩ := runScriptStep_createTable found step
  rw [nextEq]
  exact Database.tableNamed_createTable present created definition

end Belay.Sqlite.Model
