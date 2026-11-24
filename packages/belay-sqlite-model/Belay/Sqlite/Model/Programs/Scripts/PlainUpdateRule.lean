import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule

set_option doc.verso true

/-! The exact step of an UPDATE statement without RETURNING or write rules. Its subqueries
may read the clock or a counter. The data facts about {name}`Belay.Sqlite.Model.updateOutcome_ok` and
{name}`Belay.Sqlite.Model.updateOutcome_error` describe the resulting database. -/

namespace Belay.Sqlite.Model

/-- For every connection, clock, index and parameter list, if resolution from the connection gives
an UPDATE with any subqueries, no RETURNING columns and no write rules,
the step ends with {name}`clockUnmodeled` if the statement reads a missing clock. Otherwise the
first unknown counter that it reads ends the run with {name}`counterUnknownReason`. If both checks pass, a missing target table ends the run as unmodeled.
For a present table, failure of the support, subquery or JSON check ends the run as unmodeled. So does
a successful write whose key updates depend on row order. Otherwise an alias mismatch gives a datatype
error and a constraint failure gives a constraint error. Each keeps the database and
counts zero changes. A success stores the rows of {name}`LiteralData.updated` and reports and counts
the selected rows. Each continuing case has no further executions.
Proof sketch: specialize the step to its resolution. Split on the clock, counter read, table lookup
and readiness. Reduce the output and next connection for each remaining effect. -/
@[step_rule] theorem runScriptStep_plainUpdate_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.update target assignments filter [] subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index (.update target assignments filter [] subqueries none) with
      | none => .ended clockUnmodeled
      | some value =>
        let reads := (Resolved.Statement.update target assignments filter [] subqueries none).counterReads
        match connection.state.counters.firstUnknown reads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let database := connection.state.database
          match database.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view reads) parameters database subqueries
            let changed := (table.scanRows.filter (LiteralData.selected eval filter)).length
            let keys := database.keys target table
            let result := LiteralData.updated eval table assignments filter
            let outcome := updateOutcome database target keys eval table assignments filter result
            if LiteralData.updateReady keys table assignments result && Resolved.subqueriesPlain subqueries &&
                updateJsonReady eval table assignments filter [] &&
                (!outcome.isOk || LiteralData.updateKeysOrderIndependent keys table.rows result.rows) then
              match outcome with
              | .ok _ => .continued (.done changed) (connection.afterWrite (database.setRows target result.rows)
                  { changes := some changed, total := changed }) []
              | .error (reason, _) => .continued (.error reason.primaryCode)
                  (connection.afterWrite database { changes := some 0 }) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.update target assignments filter [] subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  cases timed : statementClock clock index (.update target assignments filter [] subqueries none) with
  | none => rfl
  | some value =>
    cases known : connection.state.counters.firstUnknown
        (Resolved.Statement.update target assignments filter [] subqueries none).counterReads with
    | some kind => rfl
    | none =>
      simp only [ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
        runStatement, known, Option.isNone_none, Bool.and_true]
      cases located : connection.state.database.table target with
      | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
      | some table =>
        simp only [StatementRun.withKeys, Option.map_none, Option.isSome_none, Bool.false_or]
        generalize Resolved.statementContext value (connection.state.counters.view
          (Resolved.Statement.update target assignments filter [] subqueries none).counterReads) parameters connection.state.database
          subqueries = eval
        generalize heffect : updateOutcome connection.state.database target (connection.state.database.keys target table)
          eval table assignments filter (LiteralData.updated eval table assignments filter) = effect
        generalize hready : (LiteralData.updateReady (connection.state.database.keys target table) table assignments
          (LiteralData.updated eval table assignments filter) && Resolved.subqueriesPlain subqueries &&
          updateJsonReady eval table assignments filter [] && (!effect.isOk || LiteralData.updateKeysOrderIndependent
            (connection.state.database.keys target table) table.rows (LiteralData.updated eval table assignments filter).rows)) = ready
        cases ready
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          cases effect with
          | ok written =>
            obtain rfl := updateOutcome_ok heffect
            simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
              located, Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
              Connection.afterStep, Connection.afterWrite, LiteralData.changedCounts, same, Connection.resolveState]
            rfl
          | error failure =>
            obtain ⟨reason, reached⟩ := failure
            obtain ⟨rfl, rfl | rfl⟩ := updateOutcome_error heffect <;>
              (simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed,
                StatementExecution.ofAlternatives, RunStep.withOthers, Connection.afterStep,
                Connection.afterError_failed, LiteralData.changedCounts, same, Connection.resolveState]
               rfl)

end Belay.Sqlite.Model
