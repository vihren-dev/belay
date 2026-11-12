import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites
import Belay.Sqlite.Model.Schema.Dispatch.SelectStepKeeps

set_option doc.verso true

/-!
A SELECT step keeps the connection (ADR 0017, S6). A SELECT writes no row and leaves the
counters, so a step of it that continues without an error ends at the connection where it began.
A program that reads with a SELECT and then writes continues from the same connection, which lets a
claim about the write use the facts about the start.
-/

namespace Belay.Sqlite.Model

/-- For every connection and every statement that resolves from a SELECT: if the step of the
statement continues and its output is not an error, the next connection is the connection of the
step. The database, the transaction, the settings and the counters are unchanged. Proof sketch: the
resolved statement is a query or a prepare error ({name}`resolveSelect_shape`); its effect keeps the
database ({name}`runStatement_keeps_database`) and its counts leave the counters
({name}`Counters.apply_default`); {name}`runScriptStep_effect` gives the next connection. -/
theorem runScriptStep_select_connection {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {columns source joins filter groupBy orderBy limit offset subqueries having
      distinct compound parameters output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
      parameters = .continued output next others)
    (noError : output.isError = false) : next = connection := by
  obtain ⟨resolved, after, value, found, -⟩ := runScriptStep_ran step
  obtain ⟨catalog, ok, shape⟩ := resolveStatement_select_shape found
  have ordinary := (resolveSelect_same _ _ _ _ _ _ ok).2.2
  obtain ⟨value, database, -, effect, nextEq⟩ := runScriptStep_effect found ordinary step noError
  have keeps := runStatement_keeps_database value (connection.state.counters.view resolved.counterReads)
    parameters connection.state.database resolved (by
      rcases shape with ⟨query, subqueries, same⟩ | ⟨error, same⟩
      · exact Or.inl ⟨query, subqueries, same⟩
      · exact Or.inr (Or.inr (Or.inl ⟨error, same⟩)))
  have noCounts : (connection.state.statementRun value parameters resolved).counts = {} := by
    rcases shape with ⟨query, subqueries, same⟩ | ⟨error, same⟩ <;> subst same <;>
      simp [SqlState.statementRun, runStatement]
  simp only [SqlState.statementRun] at effect
  rw [effect] at keeps
  have sameDatabase : database = connection.state.database := keeps
  rw [nextEq, noCounts, sameDatabase, Counters.apply_default]

/-- For every SELECT statement and every step of it that continues: the step has no further execution.
Plain words: a SELECT has one next state. Proof sketch: a SELECT resolves to a query or to a prepare error,
and neither is an INSERT from a query ({name}`runScriptStep_others`). -/
theorem runScriptStep_select_others {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    {output : Output} {next : Connection} {others : List StatementExecution}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] := by
  subst isSelect
  obtain ⟨resolved, after, -, found, -⟩ := runScriptStep_ran step
  obtain ⟨-, -, shape⟩ := resolveStatement_select_shape found
  exact runScriptStep_others step found (by rcases shape with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl)

/-- For every SELECT statement and every step of it that gives rows: the step continues with those
rows and keeps the connection. Plain words: a SELECT that gives rows changes nothing. Proof sketch: the
step does not end the run because its output is rows, and a SELECT step that does not give an error
keeps the connection ({name}`runScriptStep_select_connection`). -/
theorem runScriptStep_select_rows {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    {rows : List (List Value)}
    (output : (runScriptStep context clock index connection statement parameters).output = .rows rows) :
    runScriptStep context clock index connection statement parameters = .continued (.rows rows) connection [] := by
  cases step : runScriptStep context clock index connection statement parameters with
  | ended reason => rw [step] at output; simp [RunStep.output] at output
  | continued out next others =>
    obtain rfl := runScriptStep_select_others isSelect step
    subst isSelect
    rw [step] at output
    simp only [RunStep.output] at output
    subst output
    rw [runScriptStep_select_connection step rfl]

end Belay.Sqlite.Model
