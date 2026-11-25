import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! An UPDATE returning the values of its written rows. -/

namespace Belay.Sqlite.Model

/-- For every connection, clock, index and parameter list, suppose resolution gives an UPDATE
with RETURNING columns and no write programs. A missing clock or unknown counter ends the run.
An absent target or unsupported write ends the run as unmodeled. A successful write installs
the changed rows, applies its counters and returns the normalized projections of the written rows.
Each modeled refusal reports its primary error and applies the counters for the failed write.
There are no other executions. Proof sketch: take the ordinary write's guards and evaluate
the transition and the projected rows on the resulting effect. -/
@[step_rule] theorem runScriptStep_updateReturning_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.update target assignments filter (head :: tail) subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index (.update target assignments filter (head :: tail) subqueries none) with
      | none => .ended clockUnmodeled
      | some value =>
        let reads := (Resolved.Statement.update target assignments filter (head :: tail) subqueries none).counterReads
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
            let written := chosen.map fun row => (LiteralData.assign eval table.shape.columns assignments row).values
            let keys := database.keys target table
            let result := LiteralData.updated eval table assignments filter
            let outcome := updateOutcome database target keys eval table assignments filter result
            if LiteralData.updateReady keys table assignments result && Resolved.subqueriesPlain subqueries &&
                updateJsonReady eval table assignments filter (head :: tail) &&
                (!outcome.isOk || LiteralData.updateKeysOrderIndependent keys table.rows result.rows) then
              match outcome with
              | .ok _ => .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) written))) (connection.afterWrite (database.setRows target result.rows)
                  { changes := some changed, total := changed }) []
              | .error (reason, _) => .continued (.error reason.primaryCode)
                  (connection.afterWrite database { changes := some 0 }) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.update target assignments filter (head :: tail) subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  simp only [ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
    runStatement, known, Option.isNone_none, Bool.and_true]
  cases located : connection.state.database.table target with
  | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
  | some table =>
    simp only [StatementRun.withKeys, Option.map_none, Option.isSome_none, Bool.false_or]
    generalize evalEq : Resolved.statementContext value (connection.state.counters.view
      (Resolved.Statement.update target assignments filter (head :: tail) subqueries none).counterReads) parameters connection.state.database
      subqueries = eval
    generalize heffect : updateOutcome connection.state.database target (connection.state.database.keys target table)
      eval table assignments filter (LiteralData.updated eval table assignments filter) = effect
    generalize hready : (LiteralData.updateReady (connection.state.database.keys target table) table assignments
      (LiteralData.updated eval table assignments filter) && Resolved.subqueriesPlain subqueries &&
      updateJsonReady eval table assignments filter (head :: tail) && (!effect.isOk || LiteralData.updateKeysOrderIndependent
        (connection.state.database.keys target table) table.rows (LiteralData.updated eval table assignments filter).rows)) = ready
    cases ready
    · simp
    · simp only [ite_true]
      cases effect with
      | ok written =>
        obtain rfl := updateOutcome_ok heffect
        simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
          located, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
          Connection.afterStep, Connection.afterWrite, LiteralData.changedCounts, same, Connection.resolveState, evalEq]
        rfl
      | error failure =>
        obtain ⟨reason, reached⟩ := failure
        obtain ⟨rfl, rfl | rfl⟩ := updateOutcome_error heffect <;>
          (simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed,
            StatementExecution.ofAlternatives, RunStep.withOthers, Connection.afterStep,
            Connection.afterError_failed, LiteralData.changedCounts, same, Connection.resolveState]
           rfl)

end Belay.Sqlite.Model
