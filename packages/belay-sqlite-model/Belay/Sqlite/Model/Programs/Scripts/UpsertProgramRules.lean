import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! Exact steps of UPSERT on a table with foreign-key or trigger programs. -/

namespace Belay.Sqlite.Model

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to this
UPSERT with write rules and no RETURNING columns. A missing clock or unknown counter ends the step. A missing target or failed support check of
the rows, expressions or write programs ends it as unmodeled. A successful program installs its database,
applies its counts and returns its direct change count. An unmodeled error ends the step. Other errors return
their primary code and update the connection according to the conflict algorithm. There are no further
executions. Proof sketch: compute the single ordinary write from its support check and the key program's effect. -/
@[step_rule] theorem runScriptStep_upsertWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)}
    {clauses : List Resolved.ConflictClause} {algorithm : Option ConflictAlgorithm}
    {subqueries : List Resolved.Query} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.upsert target rows clauses [] algorithm subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.upsert target rows clauses [] algorithm subqueries (some rules)
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
            let keys := db.keys target table
            let policy := db.catalog.writePolicy target table.shape algorithm
            let values := Resolved.rowsAt eval table.shape.columns rows
            let steps := LiteralData.upsertSteps eval keys policy clauses table values
            let result := insertKeys rules value target policy clauses values db subqueries.isEmpty algorithm
            if LiteralData.upsertReady keys table clauses values steps && Resolved.subqueriesPlain subqueries &&
                Resolved.cellsReady eval rows && upsertJsonReady clauses [] && result.ready then
              match result.effect with
              | .ok database => .continued (.done (result.counts.changes.getD 0))
                (connection.afterWrite database result.counts) []
              | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
            else .ended unmodeledHere := by
  let stmt := Resolved.Statement.upsert target rows clauses [] algorithm subqueries (some rules)
  have ordinary : stmt.isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  let run := connection.state.statementRun value parameters stmt
  let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters connection.state.database subqueries
  let output := Output.done (run.counts.changes.getD 0)
  have observed (db : Database) (effect : run.effect = .ok db) :
      Output.ofStep value parameters stmt connection.state run (advanceRun index stmt connection.state run) = output := by
    rw [advanceRun_ordinary _ _ _ _ ordinary, effect]
    rfl
  dsimp only
  rw [ranScriptStep_write (output := output) ordinary same (connection.state.statementRun_alternatives value parameters stmt none rfl)
    (by intro reason; simp [output]) observed]
  simp only [run, stmt, output, SqlState.statementRun, runStatement, known, Option.isNone_none, Bool.and_true]
  cases located : connection.state.database.table target with
  | none => rfl
  | some table =>
    simp only [Option.map_some, StatementRun.withKeys]
    rfl

/-- For any context, clock, index, connection and parameters, suppose the statement resolves to this
UPSERT with write rules and nonempty RETURNING columns. A missing clock or unknown counter ends the step. A missing target or failed support check of
the rows, expressions or write programs ends it as unmodeled. A successful program installs its database,
applies its counts and returns its normalized RETURNING rows. An unmodeled error ends the step. Other errors return
their primary code and update the connection according to the conflict algorithm. There are no further
executions. Proof sketch: compute the single ordinary write from its support check and the key program's effect. -/
@[step_rule] theorem runScriptStep_upsertReturningWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)}
    {clauses : List Resolved.ConflictClause} {algorithm : Option ConflictAlgorithm}
    {head : Resolved.Expr × String} {tail : List (Resolved.Expr × String)}
    {subqueries : List Resolved.Query} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.upsert target rows clauses (head :: tail) algorithm subqueries (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.upsert target rows clauses (head :: tail) algorithm subqueries (some rules)
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
            let keys := db.keys target table
            let policy := db.catalog.writePolicy target table.shape algorithm
            let values := Resolved.rowsAt eval table.shape.columns rows
            let steps := LiteralData.upsertSteps eval keys policy clauses table values
            let result := insertKeys rules value target policy clauses values db subqueries.isEmpty algorithm
            if LiteralData.upsertReady keys table clauses values steps && Resolved.subqueriesPlain subqueries &&
                Resolved.cellsReady eval rows && upsertJsonReady clauses (head :: tail) && result.ready then
              match result.effect with
              | .ok database => .continued (.rows (Resolved.normalForm (returnedRows eval (head :: tail) (result.written.map (·.values)))))
                (connection.afterWrite database result.counts) []
              | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
            else .ended unmodeledHere := by
  let stmt := Resolved.Statement.upsert target rows clauses (head :: tail) algorithm subqueries (some rules)
  have ordinary : stmt.isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  let run := connection.state.statementRun value parameters stmt
  let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters connection.state.database subqueries
  let output := Output.rows (Resolved.normalForm (returnedRows eval (head :: tail) ((run.keyRows.getD []).map (·.values))))
  have observed (db : Database) (effect : run.effect = .ok db) :
      Output.ofStep value parameters stmt connection.state run (advanceRun index stmt connection.state run) = output := by
    rw [advanceRun_ordinary _ _ _ _ ordinary, effect]
    rfl
  dsimp only
  rw [ranScriptStep_write (output := output) ordinary same (connection.state.statementRun_alternatives value parameters stmt none rfl)
    (by intro reason; simp [output]) observed]
  simp only [run, stmt, eval, output, SqlState.statementRun, runStatement, known, Option.isNone_none, Bool.and_true]
  cases located : connection.state.database.table target with
  | none => rfl
  | some table =>
    simp only [Option.map_some, StatementRun.withKeys, Option.getD_some]
    rfl

end Belay.Sqlite.Model
