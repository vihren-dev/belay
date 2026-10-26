import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.ScriptLaws

set_option doc.verso true

/-!
The effect of one ADD COLUMN of the model (ADR 0017, S6). The module shows what a step of a resolved
ADD COLUMN stores when it succeeds: the column appended to the catalog entry of the table, and one
default value appended to every row. A claim about a migration that adds a column then needs only the
column and its default value, not the engine.
-/

namespace Belay.Sqlite.Model

/-- For every connection, resolved ADD COLUMN at a table position and error-free step that continues: the
next database is the database with the column appended, and the cell appended to each row is a value
that the column's default gives. The value is NULL when the default reads the clock, because the
statement then succeeds only on a table without rows. Otherwise the value is the default that
{name}`readDefaultValue` reads. In plain words, a successful ADD COLUMN changes the table at the target and
nothing else, and every old row keeps its cells. Proof sketch: {name}`runScriptStep_effect` gives the
successful effect of the run; the cases of {name}`step` for ADD COLUMN select the value. -/
theorem addColumn_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {column : CatalogColumn} {refusesPopulated : Bool} {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.addColumn target column refusesPopulated, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Value, (column.clockDefault = true → value = .null) ∧
      (column.clockDefault = false → readDefaultValue column = .ok value) ∧
      next.state.database = connection.state.database.addColumn target column value := by
  obtain ⟨value, database, -, effect, nextEq⟩ :=
    runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step noError
  simp only [SqlState.statementRun, runStatement, present, Model.step] at effect
  rw [nextEq]
  split at effect
  · cases effect
  · split at effect
    · split at effect
      · cases effect; exact ⟨.null, fun _ => rfl, fun same => by simp_all, rfl⟩
      · cases effect
    · split at effect
      · cases effect
      · rename_i read
        split at effect
        · cases effect
        · split at effect
          · cases effect
          · cases effect
            rename_i _ clockFalse _ chosen _ _
            exact ⟨chosen, fun same => absurd same clockFalse, fun _ => read, rfl⟩

end Belay.Sqlite.Model
