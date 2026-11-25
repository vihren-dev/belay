import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! An INSERT returning the values of its written rows. -/

namespace Belay.Sqlite.Model

/-- For every connection, clock, index and parameter list, suppose resolution gives an INSERT
with RETURNING columns and no write programs. A missing clock or unknown counter ends the run.
An absent target or unsupported write ends the run as unmodeled. A successful write installs
the changed rows, applies its counters and returns the normalized projections of the written rows.
Each modeled refusal reports its primary error and applies the counters for the failed write.
There are no other executions. Proof sketch: take the ordinary write's guards and evaluate
the transition and the projected rows on the resulting effect. -/
@[step_rule] theorem runScriptStep_insertReturning_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target rows (head :: tail) subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index (.insert target rows (head :: tail) subqueries none) with
      | none => .ended clockUnmodeled
      | some value =>
        let reads := (Resolved.Statement.insert target rows (head :: tail) subqueries none).counterReads
        match connection.state.counters.firstUnknown reads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let database := connection.state.database
          match database.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view reads) parameters database
              subqueries
            let keys := database.keys target table
            let values := Resolved.rowsAt eval table.shape.columns rows
            let result := LiteralData.inserted table values
            let outcome := insertOutcome database target keys table values result
            let counts := LiteralData.insertCounts outcome keys table values
            if LiteralData.insertReady keys table values result && Resolved.subqueriesPlain subqueries &&
                Resolved.cellsReady eval rows && !(returningExpressions (head :: tail)).any (·.any Resolved.Expr.isFallibleCall) then
              match outcome with
              | .ok _ => .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail)
                ((result.rows.drop table.rows.length).map (·.values))))) (connection.afterWrite (database.setRows target result.rows) counts) []
              | .error (reason, _) => .continued (.error reason.primaryCode) (connection.afterWrite database counts) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.insert target rows (head :: tail) subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  simp only [ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
    runStatement, known, Option.isNone_none, Bool.and_true]
  cases located : connection.state.database.table target with
  | none =>
    simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
  | some table =>
    simp only [StatementRun.withKeys, Option.map_none]
    generalize evalEq : Resolved.statementContext value (connection.state.counters.view
      (Resolved.Statement.insert target rows (head :: tail) subqueries none).counterReads) parameters connection.state.database
      subqueries = eval
    by_cases hready : (LiteralData.insertReady (connection.state.database.keys target table) table (Resolved.rowsAt eval table.shape.columns rows)
      (LiteralData.inserted table (Resolved.rowsAt eval table.shape.columns rows)) && Resolved.subqueriesPlain subqueries && Resolved.cellsReady eval rows &&
      !(returningExpressions (head :: tail)).any (·.any Resolved.Expr.isFallibleCall)) = true
    · simp only [hready, ite_true]
      cases outcome : insertOutcome connection.state.database target (connection.state.database.keys target table)
          table (Resolved.rowsAt eval table.shape.columns rows) (LiteralData.inserted table (Resolved.rowsAt eval table.shape.columns rows)) with
      | ok written =>
        obtain rfl := insertOutcome_ok outcome
        simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput, located,
          Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
          Connection.afterStep, Connection.afterWrite, LiteralData.insertCounts, same, Connection.resolveState, evalEq]
        rfl
      | error failure =>
        obtain ⟨reason, reached⟩ := failure
        obtain ⟨rfl, kind⟩ := insertOutcome_error outcome
        rcases kind with rfl | rfl <;>
        · simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed,
            StatementExecution.ofAlternatives, RunStep.withOthers, Connection.afterStep,
            Connection.afterError_failed, same, Connection.resolveState]
          rfl
    · simp [hready]

end Belay.Sqlite.Model
