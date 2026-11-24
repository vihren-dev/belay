import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every connection, clock, index and parameter list, if the statement resolves to a plain DELETE,
the step ends with {name}`clockUnmodeled` if the statement reads a missing clock. Otherwise the
first unknown counter that it reads ends the run with {name}`counterUnknownReason`. If both checks pass, a missing target table ends the run as unmodeled.
For a present table, failure of the subquery or JSON check ends the run as unmodeled. Otherwise the
step stores the rows of {name}`LiteralData.deleted`, reports and counts the selected rows, and has
no further executions.
Proof sketch: specialize the step to its resolution. Split on the clock, counter read, table lookup
and readiness. Reduce the output and next connection for each remaining effect. -/
@[step_rule] theorem runScriptStep_plainDelete_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {filter : Option Resolved.Expr} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.delete target filter [] subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index (.delete target filter [] subqueries none) with
      | none => .ended clockUnmodeled
      | some value =>
        let reads := (Resolved.Statement.delete target filter [] subqueries none).counterReads
        match connection.state.counters.firstUnknown reads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let database := connection.state.database
          match database.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view reads) parameters database subqueries
            let changed := (table.scanRows.filter (LiteralData.selected eval filter)).length
            if Resolved.subqueriesPlain subqueries && deleteJsonReady eval table filter [] then
              .continued (.done changed) (connection.afterWrite
                (database.setRows target (LiteralData.deleted eval table filter).rows)
                { changes := some changed, total := changed }) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.delete target filter [] subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  cases timed : statementClock clock index (.delete target filter [] subqueries none) with
  | none => rfl
  | some value =>
    cases known : connection.state.counters.firstUnknown
        (Resolved.Statement.delete target filter [] subqueries none).counterReads with
    | some kind => rfl
    | none =>
      simp only [ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
        runStatement, known, Option.isNone_none, Bool.and_true]
      cases located : connection.state.database.table target with
      | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
      | some table =>
        simp only [StatementRun.withKeys, Option.map_none]
        generalize Resolved.statementContext value (connection.state.counters.view
          (Resolved.Statement.delete target filter [] subqueries none).counterReads) parameters connection.state.database
          subqueries = eval
        by_cases ready : (Resolved.subqueriesPlain subqueries && deleteJsonReady eval table filter []) = true
        · simp only [ready, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
            located, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
            Connection.afterStep, Connection.afterWrite, LiteralData.changedCounts, same, Connection.resolveState]
          rfl
        · simp only [Bool.not_eq_true] at ready
          simp [ready]

end Belay.Sqlite.Model
