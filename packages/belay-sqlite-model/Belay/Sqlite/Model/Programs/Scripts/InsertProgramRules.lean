import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! Exact steps of INSERT on a table with foreign-key or trigger programs. -/

namespace Belay.Sqlite.Model

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to this
INSERT with write rules and nonempty RETURNING columns. A missing clock or unknown counter ends the step. A missing target or failed support check of
the rows, expressions or write programs ends it as unmodeled. A successful program installs its database,
applies its counts and returns its normalized RETURNING rows. An unmodeled error ends the step. Other errors return
their primary code and update the connection according to the conflict algorithm. There are no further
executions. Proof sketch: apply {name}`runScriptStep_of_single_write` and evaluate the write program at the target table. -/
@[step_rule] theorem runScriptStep_insertReturningWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {subqueries : List Resolved.Query} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.insert target rows (head :: tail) subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.insert target rows (head :: tail) subqueries (some rules)
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
                Resolved.subqueriesPlain subqueries && Resolved.cellsReady eval rows &&
                !(returningExpressions (head :: tail)).any (·.any Resolved.Expr.isFallibleCall) && result.ready then
              match result.effect with
              | .ok database => .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) (result.written.map (·.values)))))
                (connection.afterWrite database result.counts) []
              | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
            else .ended unmodeledHere := by
  apply runScriptStep_of_single_write found rfl rfl (fun _ _ _ => rfl) (fun _ _ _ h => nomatch h)
  intro value
  cases located : connection.state.database.table target <;> simp only [runStatement, located] <;> rfl

end Belay.Sqlite.Model
