import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! An UPSERT returning the values of its written rows. -/

namespace Belay.Sqlite.Model

/-- For every connection, clock, index and parameter list, suppose resolution gives an UPSERT
with RETURNING columns and no write programs. A missing clock or unknown counter ends the run.
An absent target or unsupported write ends the run as unmodeled. A successful write installs
the changed rows, applies its counters and returns the normalized projections of the written rows.
Each modeled refusal reports its primary error and applies the counters for the failed write.
There are no other executions. Proof sketch: take the ordinary write's guards and evaluate
the transition and the projected rows on the resulting effect. -/
@[step_rule] theorem runScriptStep_upsertReturning_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {target : Nat} {rows : List (List Resolved.Cell)} {clauses : List Resolved.ConflictClause}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.upsert target rows clauses (head :: tail) algorithm subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      let resolved := Resolved.Statement.upsert target rows clauses (head :: tail) algorithm subqueries none
      match statementClock clock index resolved with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown resolved.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let db := connection.state.database
          match db.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view resolved.counterReads)
              parameters db subqueries
            let keys := db.keys target table
            let values := Resolved.rowsAt eval table.shape.columns rows
            let steps := LiteralData.upsertSteps eval keys (db.catalog.writePolicy target table.shape algorithm)
              clauses table values
            if LiteralData.upsertReady keys table clauses values steps && Resolved.subqueriesPlain subqueries &&
                Resolved.cellsReady eval rows && upsertJsonReady clauses (head :: tail) then
              match LiteralData.upsertSummary table steps with
              | .ok (result, written) =>
                let counts := LiteralData.upsertCounts keys clauses table.shape steps none
                .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) (written.map (·.values))))) (connection.afterWrite (db.setRows target result.rows) counts) []
              | .error (reason, reached, _) =>
                let counts := LiteralData.upsertCounts keys clauses table.shape steps (some reason)
                if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode)
                  (connection.afterWriteError index reason (db.setRows target reached.rows) counts) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.upsert target rows clauses (head :: tail) algorithm subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  simp only [known, ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
    runStatement, Option.isNone_none, Bool.and_true]
  cases located : connection.state.database.table target with
  | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
  | some table =>
    simp only [StatementRun.withKeys, Option.map_none, StatementExecution.ofAlternatives, List.mapM_nil, Except.map, pure, Except.pure, List.map_nil]
    generalize evalEq : Resolved.statementContext value (connection.state.counters.view
      (Resolved.Statement.upsert target rows clauses (head :: tail) algorithm subqueries none).counterReads)
      parameters connection.state.database subqueries = eval
    generalize stepsEq : LiteralData.upsertSteps eval (connection.state.database.keys target table)
      (connection.state.database.catalog.writePolicy target table.shape algorithm) clauses table
      (Resolved.rowsAt eval table.shape.columns rows) = steps
    generalize (LiteralData.upsertReady (connection.state.database.keys target table) table clauses
      (Resolved.rowsAt eval table.shape.columns rows) steps && Resolved.subqueriesPlain subqueries &&
      Resolved.cellsReady eval rows && upsertJsonReady clauses (head :: tail)) = ready
    cases ready <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    cases outcome : LiteralData.upsertSummary table steps with
    | ok pair =>
      obtain ⟨result, written⟩ := pair
      simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
        LiteralData.upsertRun, Resolved.Statement.returnsRows, RunStep.withOthers,
        Connection.afterStep, Connection.afterWrite, Connection.resolveState, *]
      rfl
    | error failure =>
      obtain ⟨reason, reached, written⟩ := failure
      cases reason <;> simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed,
        RunStep.withOthers, Connection.afterStep, Connection.afterWriteError,
        Connection.resolveState, *] <;> rfl

end Belay.Sqlite.Model
