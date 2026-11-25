import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule
import Belay.Sqlite.Model.Schema.Columns.DerivedColumnTable

set_option doc.verso true

/-! Exact steps for resolved schema statements. Each equation gives every ending reason, output
and next connection from the resolution of a single statement. -/

namespace Belay.Sqlite.Model

/-- The database after appending a view, with empty storage at its new catalog position. -/
def Database.appendView (database : Database) (name : Identifier) (view : CatalogView) : Database :=
  { catalog := database.catalog.createView name view, rows := database.rows ++ [[]] }

/-- The database after appending an index, with empty storage at its new catalog position. -/
def Database.appendIndex (database : Database) (name : Identifier) (idx : CatalogIndex) : Database :=
  { catalog := database.catalog.createIndex name idx, rows := database.rows ++ [[]] }

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified createView operation, the following equation gives its step.
Creation at the end of an aligned catalog reports zero changes and appends the view with empty storage.
Otherwise the step ends as unmodeled.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_createView_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos : Nat} {name : Identifier} {view : CatalogView} (found : resolveStatement context connection.resolveState statement =
      .ok (.createView pos name view, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      if pos = db.catalog.length ∧ db.rows.length = db.catalog.length then
        .continued (.done 0) (connection.withDatabase (db.appendView name view)) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.createView pos name view).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.createView pos name view).readsClock = false := rfl
  have reads : (Resolved.Statement.createView pos name view).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  by_cases aligned : pos = connection.state.database.catalog.length ∧ connection.state.database.rows.length = connection.state.database.catalog.length
  · simp only [Bool.and_eq_true, beq_iff_eq, aligned]
    simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep,
      statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.withDatabase,
      same, Connection.resolveState, Database.appendView] <;> first | rfl | (simp [haltError]; rfl)
  · simp [aligned, ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed]

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified createTrigger operation, the following equation gives its step.
Creation at the end of an aligned catalog reports zero changes and appends the trigger with empty storage.
Otherwise the step ends as unmodeled.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_createTrigger_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos : Nat} {name : Identifier} {trigger : CatalogTrigger} (found : resolveStatement context connection.resolveState statement =
      .ok (.createTrigger pos name trigger, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      if pos = db.catalog.length ∧ db.rows.length = db.catalog.length then
        .continued (.done 0) (connection.withDatabase (db.appendTrigger name trigger)) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.createTrigger pos name trigger).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.createTrigger pos name trigger).readsClock = false := rfl
  have reads : (Resolved.Statement.createTrigger pos name trigger).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  by_cases aligned : pos = connection.state.database.catalog.length ∧ connection.state.database.rows.length = connection.state.database.catalog.length
  · simp only [Bool.and_eq_true, beq_iff_eq, aligned]
    simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep,
      statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.withDatabase,
      same, Connection.resolveState, Database.appendTrigger] <;> first | rfl | (simp [haltError]; rfl)
  · simp [aligned, ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed]

/-- For every resolution context, clock, index, connection and parameter list, if the statement resolves
to the specified createIndex operation, the following equation gives its step.
An unaligned catalog, a position other than its end, or a missing indexed table ends the run.
A unique index on repeated key values reports a constraint error and keeps the connection. Otherwise the
step reports zero changes and appends the index with empty storage.
There are no further executions. Proof sketch: specialize the step to the resolution and reduce
the table, transition and output checks for each branch. -/
@[step_rule] theorem runScriptStep_createIndex_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos : Nat} {name : Identifier} {idx : CatalogIndex} (found : resolveStatement context connection.resolveState statement =
      .ok (.createIndex pos name idx, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      if pos = db.catalog.length ∧ db.rows.length = db.catalog.length then
        match db.table idx.table with
        | none => .ended unmodeledHere
        | some table =>
          if idx.unique && !LiteralData.uniqueRows idx.uniqueKey table.rows then
            .continued (.error ExecutionError.constraintViolation.primaryCode) connection []
          else .continued (.done 0) (connection.withDatabase (db.appendIndex name idx)) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.createIndex pos name idx).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.createIndex pos name idx).readsClock = false := rfl
  have reads : (Resolved.Statement.createIndex pos name idx).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  by_cases aligned : pos = connection.state.database.catalog.length ∧ connection.state.database.rows.length = connection.state.database.catalog.length
  · simp only [Bool.and_eq_true, beq_iff_eq, aligned]
    cases located : connection.state.database.table idx.table with
    | none => simp [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed]
    | some table =>
      by_cases collision : idx.unique = true ∧ LiteralData.uniqueRows idx.uniqueKey table.rows = false <;>
        simp [collision, ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed,
      statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
      Connection.afterStep, Connection.afterError_failed, Connection.afterWrite, Connection.withDatabase,
      same, Connection.resolveState, Database.appendIndex] <;> first | rfl | (simp [haltError]; rfl)
  · simp [aligned, ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep, haltError_failed]

end Belay.Sqlite.Model
