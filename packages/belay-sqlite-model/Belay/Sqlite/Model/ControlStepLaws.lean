import Belay.Sqlite.Model.OrdinaryStepEffects
import Belay.Sqlite.Model.TableByName

set_option doc.verso true

/-! The step laws of BEGIN and COMMIT (ADR 0017, S6): what one step of a transaction statement does to
the connection. Neither statement writes a row or changes the catalog, so the database of the
connection is the same after the step, whether the statement succeeds or fails. -/

namespace Belay.Sqlite.Model

/-- For every connection and BEGIN statement that resolves to BEGIN, and every step that continues outside
a transaction: the step has no error output and no further execution, and the next connection is the
connection with the snapshot of the database before. In plain words, BEGIN records the database as
the committed one and changes nothing else (success law). Proof sketch: unfold the step along
{name}`runScriptStep_continued_spec`; BEGIN without a snapshot is a continuing transition, which has no
error output ({name}`Output.ofStep_isError_of_noHalt`). -/
theorem runScriptStep_begin_idle {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (idle : connection.state.snapshot = none)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with state := { connection.state with snapshot := some connection.state.database } } := by
  obtain ⟨resolved, after', value, same, -, -, -, ofStep, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := resolveStatement_after context _ _ _ _ found
  refine ⟨?_, runScriptStep_others step found rfl, ?_⟩
  · rw [← ofStep]
    exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ (by intro _ _ same; cases same)
      (by simp [advanceRun, advanceWith, idle, SqlTransition.counted, haltError])
  · rw [nextEq, afterEq]
    simp [advanceRun, advanceWith, idle, SqlTransition.counted, Connection.afterStep, SqlState.statementRun,
      runStatement, ResolveState.after, Connection.resolveState]

/-- For every connection and statement that resolves to BEGIN, and every step that continues inside a
transaction: the step has an error output and no further execution, and the next connection is the
connection. In plain words, BEGIN inside a transaction fails and changes nothing, not even the counters
(failure law). Proof sketch: the transition is the pending outcome of the failure
{name}`ExecutionError.transactionAlreadyActive`, which {name}`Connection.afterError` turns into the same
database and snapshot. -/
theorem runScriptStep_begin_active {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {original : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (active : connection.state.snapshot = some original)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = true ∧ others = [] ∧ next = connection := by
  obtain ⟨resolved, after', value, same, -, -, -, ofStep, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := resolveStatement_after context _ _ _ _ found
  refine ⟨?_, runScriptStep_others step found rfl, ?_⟩
  · rw [← ofStep]
    simp [Output.ofStep, advanceRun, advanceWith, active, SqlTransition.counted, haltError, SqlState.finish,
      ExecutionError.primaryCode, Output.isError]
  · rw [nextEq]
    simp [advanceRun, advanceWith, active, SqlTransition.counted, Connection.afterStep, Connection.afterError,
      SqlState.finish, SqlState.statementRun, runStatement, Counters.apply_default, afterEq, ResolveState.after,
      Connection.resolveState]
    obtain ⟨⟨_, _, _, _⟩, _, _⟩ := connection
    simp only at active
    simp [active]

/-- For every connection and statement that resolves to COMMIT, and every step that continues inside a
transaction: the step has no error output and no further execution, and the next connection is the
connection without the snapshot. In plain words, COMMIT keeps the database as it is and closes the
transaction (success law). Proof sketch: as {name}`runScriptStep_begin_idle`; COMMIT with a snapshot is a
continuing transition. -/
theorem runScriptStep_commit_active {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {original : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (active : connection.state.snapshot = some original)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with state := { connection.state with snapshot := none } } := by
  obtain ⟨resolved, after', value, same, -, -, -, ofStep, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := resolveStatement_after context _ _ _ _ found
  refine ⟨?_, runScriptStep_others step found rfl, ?_⟩
  · rw [← ofStep]
    exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ (by intro _ _ same; cases same)
      (by simp [advanceRun, advanceWith, active, SqlTransition.counted, haltError])
  · rw [nextEq, afterEq]
    simp [advanceRun, advanceWith, active, SqlTransition.counted, Connection.afterStep, SqlState.statementRun,
      runStatement, ResolveState.after, Connection.resolveState]

/-- For every connection and statement that resolves to COMMIT, and every step that continues outside a
transaction: the step has an error output and no further execution, and the next connection is the
connection. In plain words, COMMIT without a transaction fails and changes nothing (failure law). Proof
sketch: the transition is the failure {name}`ExecutionError.noActiveTransaction`, which
{name}`Connection.afterError` turns into the same database without a snapshot. -/
theorem runScriptStep_commit_idle {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (idle : connection.state.snapshot = none)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = true ∧ others = [] ∧ next = connection := by
  obtain ⟨resolved, after', value, same, -, -, -, ofStep, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := resolveStatement_after context _ _ _ _ found
  refine ⟨?_, runScriptStep_others step found rfl, ?_⟩
  · rw [← ofStep]
    simp [Output.ofStep, advanceRun, advanceWith, idle, SqlTransition.counted, haltError,
      ExecutionError.primaryCode, Output.isError]
  · rw [nextEq]
    simp [advanceRun, advanceWith, idle, SqlTransition.counted, Connection.afterStep, Connection.afterError,
      SqlState.statementRun, runStatement, Counters.apply_default, afterEq, ResolveState.after,
      Connection.resolveState]
    obtain ⟨⟨_, _, _, _⟩, _, _⟩ := connection
    simp only at idle
    simp [idle]

end Belay.Sqlite.Model
