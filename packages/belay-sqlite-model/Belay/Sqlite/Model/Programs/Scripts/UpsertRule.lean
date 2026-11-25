import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule

set_option doc.verso true

/-! The resolved row-by-row INSERT with conflict handling, without write rules or RETURNING. -/

namespace Belay.Sqlite.Model

/-- The connection after a failed write, with its counts. FAIL preserves the database
reached before the failing row. ROLLBACK restores an open snapshot. Other errors
retain the starting database and transaction, as in {name}`SqlState.publish`. -/
def Connection.afterWriteError (connection : Connection) (index : Nat) (reason : ExecutionError)
    (reached : Database) (counts : Counts) : Connection :=
  connection.afterError connection.resolveState counts
    (connection.state.failed index reason (if reason = .constraintFail then reached else connection.state.database))

/-- A missing clock or unknown counter ends the run. A missing target or unsupported
row, expression or conflict clause ends it as unmodeled. A successful row sequence
stores its final table, applies its counts and reports the number of changes.
An unmodeled row error ends the run. Each SQLite refusal reports its primary code
and applies the count and transaction semantics of the conflict algorithm. The
statement has one execution. Proof sketch: reduce the step at the resolved UPSERT
and split the support check and the summary of the row sequence. -/
@[step_rule] theorem runScriptStep_plainUpsert_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {clauses : List Resolved.ConflictClause}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.upsert target rows clauses [] algorithm subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      let resolved := Resolved.Statement.upsert target rows clauses [] algorithm subqueries none
      match statementClock clock index resolved with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown resolved.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let db := connection.state.database
          match db.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view resolved.counterReads)
              parameters db subqueries
            let keys := db.keys target table
            let values := Resolved.rowsAt eval table.shape.columns rows
            let steps := LiteralData.upsertSteps eval keys (db.catalog.writePolicy target table.shape algorithm)
              clauses table values
            if LiteralData.upsertReady keys table clauses values steps && Resolved.subqueriesPlain subqueries &&
                Resolved.cellsReady eval rows && upsertJsonReady clauses [] then
              match LiteralData.upsertSummary table steps with
              | .ok (result, _) =>
                let counts := LiteralData.upsertCounts keys clauses table.shape steps none
                .continued (.done (counts.changes.getD 0)) (connection.afterWrite (db.setRows target result.rows) counts) []
              | .error (reason, reached, _) =>
                let counts := LiteralData.upsertCounts keys clauses table.shape steps (some reason)
                if reason = .unmodeled then .ended unmodeledHere
                else .continued (.error reason.primaryCode)
                  (connection.afterWriteError index reason (db.setRows target reached.rows) counts) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.upsert target rows clauses [] algorithm subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  cases timed : statementClock clock index (Resolved.Statement.upsert target rows clauses [] algorithm subqueries none) with
  | none => rfl
  | some value =>
    cases known : connection.state.counters.firstUnknown (Resolved.Statement.upsert target rows clauses [] algorithm subqueries none).counterReads with
    | some kind => rfl
    | none =>
      simp only [known, ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
        runStatement, Option.isNone_none, Bool.and_true]
      cases located : connection.state.database.table target with
      | none => simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
      | some table =>
        simp only [StatementRun.withKeys, Option.map_none, StatementExecution.ofAlternatives, List.mapM_nil, Except.map, pure, Except.pure, List.map_nil]
        generalize evalEq : Resolved.statementContext value (connection.state.counters.view
          (Resolved.Statement.upsert target rows clauses [] algorithm subqueries none).counterReads)
          parameters connection.state.database subqueries = eval
        generalize stepsEq : LiteralData.upsertSteps eval (connection.state.database.keys target table)
          (connection.state.database.catalog.writePolicy target table.shape algorithm) clauses table
          (Resolved.rowsAt eval table.shape.columns rows) = steps
        generalize (LiteralData.upsertReady (connection.state.database.keys target table) table clauses
          (Resolved.rowsAt eval table.shape.columns rows) steps && Resolved.subqueriesPlain subqueries &&
          Resolved.cellsReady eval rows && upsertJsonReady clauses []) = ready
        cases ready <;> simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, Bool.not_true]
        cases outcome : LiteralData.upsertSummary table steps with
        | ok pair =>
          obtain ⟨result, written⟩ := pair
          simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
            LiteralData.upsertRun, Resolved.Statement.returnsRows, RunStep.withOthers,
            Connection.afterStep, Connection.afterWrite, Connection.resolveState, *]
          rfl
        | error failure =>
          obtain ⟨reason, reached, written⟩ := failure
          cases reason <;> simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed,
            RunStep.withOthers, Connection.afterStep, Connection.afterWriteError,
            Connection.resolveState, *] <;> rfl

end Belay.Sqlite.Model
