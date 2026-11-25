import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule

set_option doc.verso true

/-! The exact step of ADD COLUMN, including each SQLite error from checking existing rows. -/

namespace Belay.Sqlite.Model

/-- For every clock, index, connection and parameter list, if the statement resolves to ADD COLUMN at the
target, an unsupported default or missing target ends the run. On a present table with rows, the
foreign-key default restriction reports a reference-column error. Otherwise a clock default appends NULL
on an empty table and reports a nonconstant-default error on a populated table. For a readable literal
default, a required NULL on a populated table reports the NULL-default error. A row that fails the column
checks reports the check-default error. Otherwise the step appends the column with the default and reports
zero changes. Each error keeps the connection and each continuing case gives one execution.
Proof sketch: reduce the resolved step and split its readiness, table and column checks. The resolution
certificate gives the settings and each effect determines the next database. -/
@[step_rule] theorem runScriptStep_addColumn_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {column : CatalogColumn} {refuses : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.addColumn target column refuses, after)) :
    runScriptStep context clock index connection statement parameters =
      let db := connection.state.database
      if column.clockDefault || (readDefaultValue column).toOption.isSome then
        match db.table target with
        | none => .ended unmodeledHere
        | some table =>
          if refuses && !table.rows.isEmpty then
            .continued (.error ExecutionError.referenceColumnDefault.primaryCode) connection []
          else if column.clockDefault then
            if table.rows.isEmpty then
              .continued (.done 0) (connection.withDatabase (db.addColumn target column .null)) []
            else .continued (.error ExecutionError.nonConstantColumnDefault.primaryCode) connection []
          else match readDefaultValue column with
            | .error _ => .ended unmodeledHere
            | .ok value =>
              if column.notNull && value == .null && !table.rows.isEmpty then
                .continued (.error ExecutionError.nullColumnDefault.primaryCode) connection []
              else if !table.rows.all (fun row => column.checks.all
                  (LiteralData.checkHolds { row with values := row.values ++ [value] })) then
                .continued (.error ExecutionError.checkColumnDefault.primaryCode) connection []
              else .continued (.done 0) (connection.withDatabase (db.addColumn target column value)) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.addColumn target column refuses).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  have quiet : (Resolved.Statement.addColumn target column refuses).readsClock = false := rfl
  have reads : (Resolved.Statement.addColumn target column refuses).counterReads = [] := rfl
  simp only [statementClock, quiet, reads, Bool.false_eq_true, ite_false, Counters.firstUnknown,
    List.find?_nil, SqlState.statementRun, runStatement, Model.step, advanceRun_ordinary index _ connection.state _ ordinary]
  cases timed : column.clockDefault <;> cases read : readDefaultValue column <;>
    simp only [Except.toOption, Option.isSome_none, Option.isSome_some, Bool.or_self,
      Bool.or_true, Bool.true_or, Bool.false_eq_true, ite_false, ite_true,
      Bool.and_true, Bool.not_true, Bool.not_false, Option.isNone_none]
  all_goals cases present : connection.state.database.table target <;> simp only []
  all_goals repeat' first | split
  all_goals simp_all [ranScriptStep, SqlTransition.counted, SqlState.publish, Output.ofStep,
    haltError_failed, statementOutput, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives,
    RunStep.withOthers, Connection.afterStep, Connection.afterError_failed, Connection.afterWrite,
    Connection.withDatabase, Connection.resolveState] <;> first | rfl | (simp [haltError]; rfl)

end Belay.Sqlite.Model
