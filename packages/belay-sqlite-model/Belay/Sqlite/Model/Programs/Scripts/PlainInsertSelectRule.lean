import Belay.Sqlite.Model.Programs.Scripts.InsertSelectReady

set_option doc.verso true

/-! The exact step of INSERT from a query without RETURNING columns or write rules. -/

namespace Belay.Sqlite.Model

/-- A missing clock or unknown counter ends the step. An absent target, absent source productions or
a failed support check ends it as unmodeled. Each source production executes its rows in order.
The first gives the main execution. A success reports its change count and installs its database
and counters. An unmodeled main error ends the run. Each modeled error reports its primary code
and applies its counts and conflict algorithm to the reached database. Each further production has
its own output and connection in source order. Proof sketch: compute the main and further executions
with {name}`insertSelectReady_results`, then expose the table, productions and support checks. -/
@[step_rule] theorem runScriptStep_plainInsertSelect_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {cells : List Resolved.SourceCell} {query : Resolved.Query} {clauses : List Resolved.ConflictClause}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insertSelect target cells query clauses [] algorithm subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.insertSelect target cells query clauses [] algorithm subqueries none
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
            match query.productions eval db (!Resolved.Statement.collectsSource target query subqueries [] none) with
            | none | some [] => .ended unmodeledHere
            | some (first :: others) =>
              let produce := insertSelectOutcome value eval db target table cells clauses algorithm none subqueries.isEmpty
              let main := produce first
              let rest := others.map produce
              if main.ready && rest.all (fun other => other.ready && other.effect.isModeled) &&
                  insertSelectTransferReady (insertSelectTransferRowids target cells query table db none) main &&
                  Resolved.subqueriesPlain subqueries &&
                  Resolved.cellsReady eval [cells.filterMap fun | .cell fixed => some fixed | .source _ => none] &&
                  upsertJsonReady clauses [] then
                let further := rest.map fun other => StatementExecution.ofWriteEffect connection index other.counts
                  (.done (other.counts.changes.getD 0)) other.effect
                match main.effect with
                | .ok database => .continued (.done (main.counts.changes.getD 0)) (connection.afterWrite database main.counts) further
                | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                  else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached main.counts) further
              else .ended unmodeledHere := by
  let stmt := Resolved.Statement.insertSelect target cells query clauses [] algorithm subqueries none
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  apply runScriptStep_of_clock_counter found
  intro value known
  dsimp only
  rw [same, insertSelectReady_results]
  simp only [SqlState.statementRun, known, Option.isNone_none, Bool.and_true, runStatement, insertSelectRun]
  cases located : connection.state.database.table target with
  | none => rfl
  | some table =>
    dsimp only
    cases prods : query.productions (Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters connection.state.database subqueries) connection.state.database (!Resolved.Statement.collectsSource target query subqueries [] none) with
    | none => rfl
    | some list =>
      cases list with
      | nil => rfl
      | cons first others =>
        simp only [Bool.true_or, Bool.and_true, List.map_map, Function.comp_def, insertSelectSuccessOutput, List.isEmpty_nil, ite_true]
        rfl

end Belay.Sqlite.Model
