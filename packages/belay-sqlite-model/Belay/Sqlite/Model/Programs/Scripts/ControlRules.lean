import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule

set_option doc.verso true

/-! Exact rules for BEGIN, COMMIT, ROLLBACK and setting pragmas. Each equation exposes the output and connection after a resolved command. -/

namespace Belay.Sqlite.Model

/-- The connection with a setting at a value: {name}`ResolveState.set` for the connection. For example, the
setting {lit}`foreign_keys` at {lean}`true` turns enforcement on and leaves the database, the transaction
and the counters as they are. -/
def Connection.set (connection : Connection) (on : Bool) : Syntax.PragmaSetting → Connection
  | .foreignKeys => { connection with foreignKeys := on }
  | .recursiveTriggers => { connection with recursiveTriggers := on }

/-- For every clock, index, connection and parameter list, if the statement resolves to this kind:
BEGIN outside a transaction reports zero changes and saves the database. Inside a transaction it
reports an active-transaction error and keeps the connection. There is one execution in each case.
Proof sketch: specialize the step to its resolution. The resolution certificate gives the settings
of the next connection. Reduce the transition and output for each case. -/
@[step_rule] theorem runScriptStep_begin_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after)) :
    runScriptStep context clock index connection statement parameters =
      match connection.state.snapshot with
      | none => .continued (.done 0) { connection with state := { connection.state with snapshot := some connection.state.database } } []
      | some _ => .continued (.error ExecutionError.transactionAlreadyActive.primaryCode) connection [] := by
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  simp only [runScriptStep, runScriptStepWith, found]
  rw [afterEq]
  obtain ⟨⟨database, snapshot, clockState, counters⟩, fk, triggers⟩ := connection
  obtain ⟨changes, total, last⟩ := counters
  cases snapshot <;> cases total <;> rfl

/-- For every clock, index, connection and parameter list, if the statement resolves to this kind:
COMMIT outside a transaction reports a missing-transaction error and keeps the connection. Inside a
transaction it reports zero changes and clears the snapshot. There is one execution in each case.
Proof sketch: specialize the step to its resolution. The resolution certificate gives the settings
of the next connection. Reduce the transition and output for each case. -/
@[step_rule] theorem runScriptStep_commit_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after)) :
    runScriptStep context clock index connection statement parameters =
      match connection.state.snapshot with
      | none => .continued (.error ExecutionError.noActiveTransaction.primaryCode) connection []
      | some _ => .continued (.done 0) { connection with state := { connection.state with snapshot := none } } [] := by
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  simp only [runScriptStep, runScriptStepWith, found]
  rw [afterEq]
  obtain ⟨⟨database, snapshot, clockState, counters⟩, fk, triggers⟩ := connection
  obtain ⟨changes, total, last⟩ := counters
  cases snapshot <;> cases total <;> rfl

/-- For every clock, index, connection and parameter list, if the statement resolves to this kind:
ROLLBACK outside a transaction reports a missing-transaction error and keeps the connection. Inside a
transaction it reports zero changes, restores the saved database and clears the snapshot. There is one execution in each case.
Proof sketch: specialize the step to its resolution. The resolution certificate gives the settings
of the next connection. Reduce the transition and output for each case. -/
@[step_rule] theorem runScriptStep_rollback_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.rollback, after)) :
    runScriptStep context clock index connection statement parameters =
      match connection.state.snapshot with
      | none => .continued (.error ExecutionError.noActiveTransaction.primaryCode) connection []
      | some saved => .continued (.done 0) { connection with state := { connection.state with database := saved, snapshot := none } } [] := by
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  simp only [runScriptStep, runScriptStepWith, found]
  rw [afterEq]
  obtain ⟨⟨database, snapshot, clockState, counters⟩, fk, triggers⟩ := connection
  obtain ⟨changes, total, last⟩ := counters
  cases snapshot <;> cases total <;> rfl

/-- For every clock, index, connection and parameter list, if the statement resolves to this kind:
A setting pragma reports zero changes and installs the value computed by resolution. It keeps the
database, snapshot, clock and counters. There is one execution in each case.
Proof sketch: specialize the step to its resolution. The resolution certificate gives the settings
of the next connection. Reduce the transition and output for each case. -/
@[step_rule] theorem runScriptStep_setting_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {setting : Syntax.PragmaSetting} {on : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting on, after)) :
    runScriptStep context clock index connection statement parameters =
      .continued (.done 0) (connection.set on setting) [] := by
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  simp only [runScriptStep, runScriptStepWith, found]
  rw [afterEq]
  obtain ⟨⟨database, snapshot, clockState, counters⟩, fk, triggers⟩ := connection
  obtain ⟨changes, total, last⟩ := counters
  cases setting <;> cases total <;> rfl

end Belay.Sqlite.Model
