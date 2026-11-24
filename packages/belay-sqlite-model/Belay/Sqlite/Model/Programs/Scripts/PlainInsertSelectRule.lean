import Belay.Sqlite.Model.Programs.Scripts.InsertSelectResults

set_option doc.verso true

/-! The exact step of INSERT from a query without RETURNING columns or write rules. -/

namespace Belay.Sqlite.Model

/-- A missing clock or unknown counter ends the step. An absent target, absent source productions or
a failed support check ends it as unmodeled. Each source production executes its rows in order.
The first gives the main execution. A success reports its change count and installs its database
and counters. An unmodeled main error ends the run. Each modeled error reports its primary code
and applies its counts and conflict algorithm to the reached database. Each further production has
its own output and connection in source order. Proof sketch: compute the main and further executions
with {name}`ranScriptStep_insertSelect`, then expose the table, productions and support checks. -/
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
  simp only [runScriptStep, runScriptStepWith, found]
  change (match statementClock clock index stmt with | none => _ | some _ => _) = _
  cases timed : statementClock clock index stmt with
  | none => rfl
  | some value =>
    dsimp only
    cases known : connection.state.counters.firstUnknown stmt.counterReads with
    | some kind => rfl
    | none =>
      let run := connection.state.statementRun value parameters stmt
      have computed : ranScriptStep index parameters connection stmt after value run
          (advanceRun index stmt connection.state run) =
          ranScriptStep index parameters connection stmt (connection.resolveState.after stmt) value run
          (advanceRun index stmt connection.state run) := by rw [same]
      rw [computed]
      have normalized := @ranScriptStep_insertSelect index target value connection parameters cells query clauses [] algorithm subqueries none run
      by_cases ready : run.ready = true
      · have admitted := runStatement_insertSelect_none_alternatives value (connection.state.counters.view stmt.counterReads)
          parameters target cells query clauses [] algorithm subqueries connection.state.database (Bool.and_eq_true_iff.1 ready).1
        rw [normalized admitted]
        simp only [run, SqlState.statementRun, stmt, runStatement, insertSelectRun] at ready ⊢
        simp only [stmt] at known
        simp only [known, Option.isNone_none, Bool.and_true, Bool.true_or, ite_true, insertSelectSuccessOutput,
          List.isEmpty_nil, List.map_map, Function.comp_def] at ready ⊢
        split at ready <;> rename_i tableEq <;> simp only [tableEq] at ready ⊢
        · rfl
        · split at ready <;> rename_i prodEq <;> simp only [prodEq] at ready ⊢ <;> try contradiction
          simp only [List.map_map, Function.comp_def] at ready ⊢
          simp only [ready, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [ite_eq_left (by exact ready)]
          split <;> rename_i effect <;> rw [effect]
      · have unsupported : run.ready = false := Bool.eq_false_iff.mpr ready
        change (if !run.ready then _ else _) = _
        rw [unsupported]
        simp only [Bool.not_false, ite_true]
        simp only [run, SqlState.statementRun, stmt, runStatement, insertSelectRun] at unsupported
        simp only [stmt] at known
        simp only [known, Option.isNone_none, Bool.and_true, Bool.true_or] at unsupported
        split at unsupported <;> rename_i tableEq <;> simp only [tableEq] at unsupported ⊢ <;> try contradiction
        split at unsupported <;> rename_i prodEq <;> simp only [prodEq] at unsupported ⊢ <;> try rfl
        rw [ite_eq_right (by intro h; have : false = true := unsupported.symm.trans h; contradiction)]

end Belay.Sqlite.Model
