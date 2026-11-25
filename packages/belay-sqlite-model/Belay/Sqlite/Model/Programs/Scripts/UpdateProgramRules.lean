import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! Exact steps of UPDATE on a table with foreign-key or trigger programs. -/

namespace Belay.Sqlite.Model

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to this
UPDATE with write rules and no RETURNING columns. A missing clock or unknown counter ends the step. A missing target or failed support check of
the rows, expressions or write programs ends it as unmodeled. A successful program installs its database,
applies its counts and returns its direct change count. An unmodeled error ends the step. Other errors return
their primary code and update the connection according to the conflict algorithm. There are no further
executions. Proof sketch: apply {name}`runScriptStep_of_single_write` and evaluate the write program at the target table. -/
@[step_rule] theorem runScriptStep_updateWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr}
    {subqueries : List Resolved.Query} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.update target assignments filter [] subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.update target assignments filter [] subqueries (some rules)
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
            let changed := LiteralData.updated eval table assignments filter
            let result := updateKeys eval rules target table assignments filter db subqueries.isEmpty
            if LiteralData.updateReady (db.keys target table) table assignments changed && Resolved.subqueriesPlain subqueries &&
                updateJsonReady eval table assignments filter [] && result.ready then
              match result.effect with
              | .ok database => .continued (.done (result.counts.changes.getD 0))
                (connection.afterWrite database result.counts) []
              | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
            else .ended unmodeledHere := by
  apply runScriptStep_of_single_write found rfl rfl (fun _ _ _ => rfl) (fun _ _ _ h => nomatch h)
  intro value
  cases located : connection.state.database.table target with
  | none => simp only [runStatement, located]; rfl
  | some table =>
    simp only [runStatement, located, StatementRun.withKeys, Option.map_some, Option.isSome_some, Bool.true_or, Bool.and_true]
    rfl

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to this
UPDATE with write rules and nonempty RETURNING columns. A missing clock or unknown counter ends the step. A missing target or failed support check of
the rows, expressions or write programs ends it as unmodeled. A successful program installs its database,
applies its counts and returns its normalized RETURNING rows. An unmodeled error ends the step. Other errors return
their primary code and update the connection according to the conflict algorithm. There are no further
executions. Proof sketch: apply {name}`runScriptStep_of_single_write` and evaluate the write program at the target table. -/
@[step_rule] theorem runScriptStep_updateReturningWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {subqueries : List Resolved.Query} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.update target assignments filter (head :: tail) subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.update target assignments filter (head :: tail) subqueries (some rules)
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
            let changed := LiteralData.updated eval table assignments filter
            let result := updateKeys eval rules target table assignments filter db subqueries.isEmpty
            if LiteralData.updateReady (db.keys target table) table assignments changed && Resolved.subqueriesPlain subqueries &&
                updateJsonReady eval table assignments filter (head :: tail) && result.ready then
              match result.effect with
              | .ok database => .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) (result.written.map (·.values)))))
                (connection.afterWrite database result.counts) []
              | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
            else .ended unmodeledHere := by
  apply runScriptStep_of_single_write found rfl rfl (fun _ _ _ => rfl) (fun _ _ _ h => nomatch h)
  intro value
  cases located : connection.state.database.table target with
  | none => simp only [runStatement, located]; rfl
  | some table =>
    simp only [runStatement, located, StatementRun.withKeys, Option.map_some, Option.isSome_some, Bool.true_or, Bool.and_true]
    rfl

end Belay.Sqlite.Model
