import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! A DELETE returning the values of its written rows. -/

namespace Belay.Sqlite.Model

/-- For every connection, clock, index and parameter list, suppose resolution gives a DELETE
with RETURNING columns and no write programs. A missing clock or unknown counter ends the run.
An absent target or unsupported write ends the run as unmodeled. A successful write installs
the changed rows, applies its counters and returns the normalized projections of the written rows.
DELETE has no constraint failure.
There are no other executions. Proof sketch: take the ordinary write's guards and evaluate
the transition and the projected rows on the resulting effect. -/
@[step_rule] theorem runScriptStep_deleteReturning_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {target : Nat} {filter : Option Resolved.Expr} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.delete target filter (head :: tail) subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index (.delete target filter (head :: tail) subqueries none) with
      | none => .ended clockUnmodeled
      | some value =>
        let reads := (Resolved.Statement.delete target filter (head :: tail) subqueries none).counterReads
        match connection.state.counters.firstUnknown reads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let database := connection.state.database
          match database.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view reads) parameters database subqueries
            let chosen := table.scanRows.filter (LiteralData.selected eval filter)
            let changed := chosen.length
            let written := chosen.map (·.values)
            if Resolved.subqueriesPlain subqueries && deleteJsonReady eval table filter (head :: tail) then
              .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) written))) (connection.afterWrite
                (database.setRows target (LiteralData.deleted eval table filter).rows)
                { changes := some changed, total := changed }) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.delete target filter (head :: tail) subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  simp only [ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
    runStatement, known, Option.isNone_none, Bool.and_true]
  cases located : connection.state.database.table target with
  | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
  | some table =>
    simp only [StatementRun.withKeys, Option.map_none]
    generalize evalEq : Resolved.statementContext value (connection.state.counters.view
      (Resolved.Statement.delete target filter (head :: tail) subqueries none).counterReads) parameters connection.state.database
      subqueries = eval
    by_cases ready : (Resolved.subqueriesPlain subqueries && deleteJsonReady eval table filter (head :: tail)) = true
    · simp only [ready, ite_true]
      simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
        located, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
        Connection.afterStep, Connection.afterWrite, LiteralData.changedCounts, same, Connection.resolveState, evalEq]
      rfl
    · simp only [Bool.not_eq_true] at ready
      simp [ready]

end Belay.Sqlite.Model
