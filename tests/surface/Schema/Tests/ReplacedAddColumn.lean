import Belay

set_option doc.verso true

/-! The former schema statements of ADR 0033, derived with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedSchema

/-- The deleted law {lit}`addColumn_database`. For every connection, resolved ADD COLUMN at a table position and error-free step that continues: the
next database is the database with the column appended, and the cell appended to each row is a value
that the column's default gives. The value is NULL when the default reads the clock, because the
statement then succeeds only on a table without rows. Otherwise the value is the default that
{name}`readDefaultValue` reads. In plain words, a successful ADD COLUMN changes the table at the target and
nothing else, and every old row keeps its cells. Proof sketch: the success branches of {name}`runScriptStep_addColumn_eq` give the stored default. -/
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
  rw [runScriptStep_addColumn_eq found] at step
  simp only [present] at step
  repeat' split at step
  all_goals cases step
  all_goals first | contradiction | exact ⟨.null, fun _ => rfl, by simp_all, rfl⟩ | exact ⟨_, by simp_all, fun _ => by assumption, rfl⟩

/-- The deleted law {lit}`runScriptStep_addColumn_failed`. For every connection, ADD COLUMN and step that continues with an error output: the next connection is
the connection with the counters of the run, for some clock value. In plain words, a refused ADD COLUMN
changes nothing but the counters. Proof sketch: the applicable branch of {name}`runScriptStep_addColumn_eq` gives the result. -/
theorem runScriptStep_addColumn_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {target : Nat} {column : CatalogColumn} {refusesPopulated : Bool}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.addColumn target column refusesPopulated, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (failed : output.isError = true) :
    ∃ value, next = { connection with state := { connection.state with
        counters := connection.state.counters.apply
          (connection.state.statementRun value parameters (.addColumn target column refusesPopulated)).counts } } := by
  rw [runScriptStep_addColumn_eq found] at step
  cases present : connection.state.database.table target <;> simp only [present] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | contradiction | exact ⟨0, by simp [SqlState.statementRun, runStatement]⟩

#print axioms addColumn_database
#print axioms runScriptStep_addColumn_failed

end Belay.Sqlite.Model.ReplacedSchema
