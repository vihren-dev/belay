import Belay.Sqlite.Model.Programs.Scripts.UpsertRule

set_option doc.verso true

/-! The INSERT step with resolved foreign-key or trigger programs and no RETURNING. -/

namespace Belay.Sqlite.Model

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to an INSERT
of literal rows with write rules and no RETURNING columns. An absent clock or unknown counter ends the step with its reason. A missing target,
unsupported input or unsupported write program ends it as unmodeled. When the write programs
succeed, the step installs their database, applies their counts and reports their changes.
An unmodeled program error ends the step. Every other error reports its primary code and
applies its counts and conflict algorithm to the reached database. There are no further
executions. Proof sketch: reduce the step at the resolution, check the plain rows and key
program support, and take the effect of {name}`insertKeys`. -/
@[step_rule] theorem runScriptStep_insertWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target rows [] subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.insert target rows [] subqueries (some rules)
      match statementClock clock index stmt with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown stmt.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let db := connection.state.database
          match db.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters db subqueries
            let values := Resolved.rowsAt eval table.shape.columns rows
            let result := insertKeys rules value target (db.catalog.writePolicy target table.shape none) [] values db subqueries.isEmpty
            if LiteralData.insertReady (db.keys target table) table values (LiteralData.inserted table values) &&
                Resolved.subqueriesPlain subqueries && Resolved.cellsReady eval rows && result.ready then
              match result.effect with
              | .ok database => .continued (.done (result.counts.changes.getD 0)) (connection.afterWrite database result.counts) []
              | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
            else .ended unmodeledHere := by
  let stmt := Resolved.Statement.insert target rows [] subqueries (some rules)
  have ordinary : stmt.isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  change (match statementClock clock index stmt with | none => _ | some _ => _) = _
  cases timed : statementClock clock index stmt with
  | none => rfl
  | some value =>
    dsimp only
    cases known : connection.state.counters.firstUnknown stmt.counterReads with
    | some kind => rfl
    | none =>
      simp only [stmt] at ordinary known
      simp only [known, ranScriptStep, advanceRun_ordinary _ _ _ _ ordinary, SqlState.statementRun,
        runStatement, Option.isNone_none, Bool.and_true]
      cases located : connection.state.database.table target with
      | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
      | some table =>
        simp only [StatementRun.withKeys, Option.map_some, returningExpressions, List.map_nil, List.any_nil, Bool.not_false,
          Bool.and_true, StatementExecution.ofAlternatives, List.mapM_nil, Except.map, pure, Except.pure]
        generalize evalEq : Resolved.statementContext value (connection.state.counters.view stmt.counterReads)
          parameters connection.state.database subqueries = eval
        generalize valuesEq : Resolved.rowsAt eval table.shape.columns rows = values
        generalize keyEq : insertKeys rules value target (connection.state.database.catalog.writePolicy target table.shape none)
          [] values connection.state.database subqueries.isEmpty = result
        generalize (LiteralData.insertReady (connection.state.database.keys target table) table values (LiteralData.inserted table values) &&
          Resolved.subqueriesPlain subqueries && Resolved.cellsReady eval rows && result.ready) = ready
        cases ready <;> simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, Bool.not_true]
        cases effect : result.effect with
        | ok db =>
          simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput, Resolved.Statement.returnsRows,
            RunStep.withOthers, Connection.afterStep, Connection.afterWrite, Connection.resolveState, same]
        | error failure =>
          obtain ⟨reason, reached⟩ := failure
          cases reason <;> simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed, RunStep.withOthers,
            Connection.afterStep, Connection.afterWriteError, Connection.resolveState, same] <;> rfl

end Belay.Sqlite.Model
