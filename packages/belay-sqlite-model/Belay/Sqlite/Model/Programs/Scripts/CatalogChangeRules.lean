import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule
import Belay.Sqlite.Model.Schema.Columns.DerivedColumnTable

set_option doc.verso true

/-! Exact steps for resolved schema statements. Each equation gives every ending reason, output
and next connection from the resolution of a single statement. -/

namespace Belay.Sqlite.Model

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified dropPlain operation, the following equation gives its step.
DROP without write rules removes the listed positions and their rows. It reports zero changes
and keeps the snapshot, settings and counters.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_dropPlain_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat} (found : resolveStatement context connection.resolveState statement =
      .ok (.drop positions none, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      .continued (.done 0) (connection.withDatabase (db.drop positions)) [] := by
  have ordinary : (Resolved.Statement.drop positions none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.drop positions none).readsClock = false := rfl
  have reads : (Resolved.Statement.drop positions none).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep,
      statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.withDatabase,
      StatementRun.withKeys, same, Connection.resolveState] <;> first | rfl | (simp [haltError]; rfl)

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified rewrite operation, the following equation gives its step.
When the stored and renamed catalogs have the same outline, the step installs the renamed catalog,
keeps the rows and reports zero changes. Otherwise the step ends as unmodeled.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_rewrite_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog} (found : resolveStatement context connection.resolveState statement =
      .ok (.rewrite renamed, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      if db.catalog.sameOutline renamed then
        .continued (.done 0) (connection.withDatabase { db with catalog := renamed }) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.rewrite renamed).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.rewrite renamed).readsClock = false := rfl
  have reads : (Resolved.Statement.rewrite renamed).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  cases guard : connection.state.database.catalog.sameOutline renamed <;>
    simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed,
      statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.withDatabase,
      same, Connection.resolveState] <;> first | rfl | (simp [haltError]; rfl)

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified dropColumn operation, the following equation gives its step.
When the drop-column guard passes, the step drops the column from its stored rows, installs the
resolved catalog and reports zero changes. Otherwise the step ends as unmodeled.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_dropColumn_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target col : Nat} {stored : Catalog} (found : resolveStatement context connection.resolveState statement =
      .ok (.dropColumn target col stored, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      if db.runsDropColumn target col stored then
        .continued (.done 0) (connection.withDatabase (db.dropColumn target col stored)) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.dropColumn target col stored).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.dropColumn target col stored).readsClock = false := rfl
  have reads : (Resolved.Statement.dropColumn target col stored).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  cases guard : connection.state.database.runsDropColumn target col stored <;>
    simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed,
      statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.withDatabase,
      same, Connection.resolveState] <;> first | rfl | (simp [haltError]; rfl)

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified prepareError operation, the following equation gives its step.
A resolved preparation refusal reports its primary error code and keeps the entire connection.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_prepareError_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {reason : PrepareError} (found : resolveStatement context connection.resolveState statement =
      .ok (.prepareError reason, after)) :
    runScriptStep context clock index connection statement parameters =
      .continued (.error (ExecutionError.prepare reason).primaryCode) connection [] := by
  have ordinary : (Resolved.Statement.prepareError reason).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.prepareError reason).readsClock = false := rfl
  have reads : (Resolved.Statement.prepareError reason).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed,
      StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.afterError_failed, Connection.afterWrite,
      same, Connection.resolveState] <;> first | rfl | (simp [haltError]; rfl)

end Belay.Sqlite.Model
