import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! The INSERT step with resolved foreign-key or trigger programs and no RETURNING. -/

namespace Belay.Sqlite.Model

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to an INSERT
of literal rows with write rules and no RETURNING columns. An absent clock or unknown counter ends the step with its reason. A missing target,
unsupported input or unsupported write program ends it as unmodeled. When the write programs
succeed, the step installs their database, applies their counts and reports their changes.
An unmodeled program error ends the step. Every other error reports its primary code and
applies its counts and conflict algorithm to the reached database. There are no further
executions. Proof sketch: apply {name}`runScriptStep_of_single_write` and evaluate {name}`insertKeys` at the target table. -/
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
  apply runScriptStep_of_single_write found rfl rfl (fun _ _ _ => rfl) (fun _ _ _ h => nomatch h)
  intro value
  cases located : connection.state.database.table target with
  | none => simp only [runStatement, located]; rfl
  | some table =>
    simp only [runStatement, located, StatementRun.withKeys, Option.map_some, returningExpressions, List.map_nil, List.any_nil, Bool.not_false, Bool.and_true]
    rfl

end Belay.Sqlite.Model
