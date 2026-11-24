import Belay.Sqlite.Model.Programs.Scripts.InsertSelectReady

set_option doc.verso true

/-! INSERT from a query with write programs. -/

namespace Belay.Sqlite.Model

/-- At any context, clock, index, connection and parameters, suppose resolution gives INSERT SELECT
with write programs and no RETURNING. A missing clock or unknown counter ends the step.
A missing table, anything other than one production, or a failed support check ends it as unmodeled.
Each supported success returns its direct change count and applies its database and counts.
An unmodeled main failure ends it. A modeled refusal gives the primary code and conflict transition.
There are no further executions.
Proof sketch: reduce the supported run with {name}`insertSelectReady_results` and distinguish the source productions. -/
@[step_rule] theorem runScriptStep_insertSelectWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {cells : List Resolved.SourceCell} {query : Resolved.Query} {clauses : List Resolved.ConflictClause}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insertSelect target cells query clauses [] algorithm subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.insertSelect target cells query clauses [] algorithm subqueries (some rules)
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
            match query.productions eval db (!Resolved.Statement.collectsSource target query subqueries [] (some rules)) with
            | none | some [] | some (_ :: _ :: _) => .ended unmodeledHere
            | some [first] =>
              let produce := insertSelectOutcome value eval db target table cells clauses algorithm (some rules) subqueries.isEmpty
              let main := produce first
              if main.ready && Resolved.subqueriesPlain subqueries &&
                  Resolved.cellsReady eval [cells.filterMap fun | .cell fixed => some fixed | .source _ => none] &&
                  upsertJsonReady clauses [] then
                match main.effect with
                | .ok database => .continued (.done (main.counts.changes.getD 0)) (connection.afterWrite database main.counts) []
                | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                  else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached main.counts) []
              else .ended unmodeledHere := by
  let stmt := Resolved.Statement.insertSelect target cells query clauses [] algorithm subqueries (some rules)
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
    cases prods : query.productions (Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters connection.state.database subqueries) connection.state.database (!Resolved.Statement.collectsSource target query subqueries [] (some rules)) with
    | none => rfl
    | some list =>
      cases list with
      | nil => rfl
      | cons first others =>
        cases others <;> simp only [Option.isNone_some, Bool.false_or, Bool.and_true, List.isEmpty_nil, List.isEmpty_cons, Bool.and_false, Bool.false_and, List.map_nil, List.all_nil, ite_false, Bool.false_eq_true, insertSelectTransferRowids_withRules, insertSelectTransferReady, insertSelectSuccessOutput, List.isEmpty_nil, ite_true]
        all_goals first | rfl | (split <;> rename_i condition <;> simp only [condition, ite_true, ite_false] <;> first | rfl | (split <;> rename_i eff <;> rw [eff]))

/-- At any context, clock, index, connection and parameters, suppose resolution gives INSERT SELECT
with write programs and nonempty RETURNING. A missing clock or unknown counter ends the step.
A missing table, anything other than one production, or a failed support check ends it as unmodeled.
Each supported success returns normalized written rows and applies its database and counts.
An unmodeled main failure ends it. A modeled refusal gives the primary code and conflict transition.
There are no further executions.
Proof sketch: reduce the supported run with {name}`insertSelectReady_results` and distinguish the source productions. -/
@[step_rule] theorem runScriptStep_insertSelectReturningWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {cells : List Resolved.SourceCell} {query : Resolved.Query} {clauses : List Resolved.ConflictClause}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insertSelect target cells query clauses (head :: tail) algorithm subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.insertSelect target cells query clauses (head :: tail) algorithm subqueries (some rules)
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
            match query.productions eval db false with
            | none | some [] | some (_ :: _ :: _) => .ended unmodeledHere
            | some [first] =>
              let produce := insertSelectOutcome value eval db target table cells clauses algorithm (some rules) subqueries.isEmpty
              let main := produce first
              if main.ready && Resolved.subqueriesPlain subqueries &&
                  Resolved.cellsReady eval [cells.filterMap fun | .cell fixed => some fixed | .source _ => none] &&
                  upsertJsonReady clauses (head :: tail) then
                match main.effect with
                | .ok database => .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) ((main.keyRows.getD []).map (·.values))))) (connection.afterWrite database main.counts) []
                | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                  else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached main.counts) []
              else .ended unmodeledHere := by
  let stmt := Resolved.Statement.insertSelect target cells query clauses (head :: tail) algorithm subqueries (some rules)
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
    simp only [Resolved.Statement.collectsSource, List.isEmpty_cons, Bool.not_false, Bool.or_true, Bool.true_or,
      Bool.not_true]
    cases prods : query.productions (Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters connection.state.database subqueries) connection.state.database false with
    | none => rfl
    | some list =>
      cases list with
      | nil => rfl
      | cons first others =>
        cases others <;> simp only [Option.isNone_some, Bool.false_or, Bool.and_true, List.isEmpty_nil, List.isEmpty_cons, Bool.and_false, Bool.false_and, List.map_nil, List.all_nil, ite_false, Bool.false_eq_true, insertSelectTransferRowids_withRules, insertSelectTransferReady, insertSelectSuccessOutput, List.isEmpty_cons, Bool.false_eq_true, ite_false]
        all_goals first | rfl | (split <;> rename_i condition <;> simp only [condition, ite_true, ite_false] <;> first | rfl | (split <;> rename_i eff <;> rw [eff]))

end Belay.Sqlite.Model
