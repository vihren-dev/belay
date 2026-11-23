import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule
import Belay.Sqlite.Model.Schema.Writes.PlainWriteFrame
import Belay.Sqlite.Model.Schema.Writes.PlainInsertSuccess

set_option doc.verso true

/-! The exact kind rule of plain INSERT: an INSERT of rows without a RETURNING clause and without write rules. The
rule {lit}`runScriptStep_plainInsert_eq` applies to a statement that resolves to
{lit}`Resolved.Statement.insert target rows [] subqueries none`. A case split on its matches and its condition gives
each fact about the step. The data lemmas {lit}`insertOutcome_of_fits`, {lit}`insertReady_of_fits` and
{lit}`insertOutcome_error` select the cases of an INSERT of rows that fit the table, and of a failure. -/

namespace Belay.Sqlite.Model

/-- The kind rule of plain INSERT. For every resolution context, clock, index, connection, statement, parameter
values, resolution state, target position, rows of cells and subqueries: if the statement resolves from the
connection to an INSERT of the rows into the target with the subqueries, without a RETURNING clause and without write
rules, the step of the statement is exactly this:
* When {name}`statementClock` gives no clock value (the statement reads the clock and the run has no clock), the
  run ends with {name}`clockUnmodeled`.
* Else, when a counter that the statement reads is unknown ({name}`Counters.firstUnknown`), the run ends with
  {name}`counterUnknownReason` of the counter.
* Else, when the target holds no table, the run ends with {name}`unmodeledHere`.
* Else, take the table, the evaluation context of the clock value and the counters, the values of the rows
  ({name}`Resolved.rowsAt`), the table with the values inserted ({name}`LiteralData.inserted`), the outcome
  ({name}`insertOutcome`) and the counts ({name}`LiteralData.insertCounts`). When the support check
  ({name}`LiteralData.insertReady`), the subquery check ({name}`Resolved.subqueriesPlain`) or the cell check
  ({name}`Resolved.cellsReady`) fails, the run ends with {name}`unmodeledHere`.
* Else, when the outcome succeeds, the step continues with the output {lit}`.done rows.length`, with the connection
  after the write ({name}`Connection.afterWrite`) of the database that {name}`Database.setRows` gives for the target
  and the rows of the inserted table, with the counts, and with no further execution. A valid database has a row list
  at each table position, so the rows are then stored at the target.
* Else the outcome fails with an error, and the step continues with the output of the primary code of the error,
  with the connection after the write of the database before the statement with the counts, and with no further
  execution.
In each case that continues, the settings, the snapshot of an open transaction and the clock assignment stay. An
INSERT that reads no clock and no counter passes the first two checks for every clock and all counters. Proof
sketch: unfold the step with the resolution and split on the clock, the counters and the table; the run is the plain
computation of {name}`runStatement`; a success publishes the database and applies the counts; a failure is one of
the two errors of {name}`insertOutcome_error`, so {name}`Connection.afterError_failed` gives the connection. -/
@[step_rule] theorem runScriptStep_plainInsert_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target rows [] subqueries none, after)) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index (.insert target rows [] subqueries none) with
      | none => .ended clockUnmodeled
      | some value =>
        let reads := (Resolved.Statement.insert target rows [] subqueries none).counterReads
        match connection.state.counters.firstUnknown reads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let database := connection.state.database
          match database.table target with
          | none => .ended unmodeledHere
          | some table =>
            let eval := Resolved.statementContext value (connection.state.counters.view reads) parameters database
              subqueries
            let keys := database.keys target table
            let values := Resolved.rowsAt eval table.shape.columns rows
            let result := LiteralData.inserted table values
            let outcome := insertOutcome database target keys table values result
            let counts := LiteralData.insertCounts outcome keys table values
            if LiteralData.insertReady keys table values result && Resolved.subqueriesPlain subqueries &&
                Resolved.cellsReady eval rows then
              match outcome with
              | .ok _ => .continued (.done rows.length) (connection.afterWrite (database.setRows target result.rows) counts) []
              | .error (reason, _) => .continued (.error reason.primaryCode) (connection.afterWrite database counts) []
            else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.insert target rows [] subqueries none).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  simp only [runScriptStep, runScriptStepWith, found]
  cases timed : statementClock clock index (.insert target rows [] subqueries none) with
  | none => rfl
  | some value =>
    cases known : connection.state.counters.firstUnknown
        (Resolved.Statement.insert target rows [] subqueries none).counterReads with
    | some kind => rfl
    | none =>
      simp only [ranScriptStep, advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun,
        runStatement, known, Option.isNone_none, Bool.and_true]
      cases located : connection.state.database.table target with
      | none =>
        simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]
      | some table =>
        simp only [StatementRun.withKeys, Option.map_none, returningExpressions, List.map_nil,
          List.any_nil, Bool.not_false, Bool.and_true]
        generalize Resolved.statementContext value (connection.state.counters.view
          (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
          subqueries = eval
        have length : (Resolved.rowsAt eval table.shape.columns rows).length = rows.length := by
          simp [Resolved.rowsAt]
        rw [← length]
        generalize Resolved.rowsAt eval table.shape.columns rows = values
        generalize hready : (LiteralData.insertReady (connection.state.database.keys target table) table values
          (LiteralData.inserted table values) && Resolved.subqueriesPlain subqueries && Resolved.cellsReady eval rows) =
          ready
        cases ready
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          cases outcome : insertOutcome connection.state.database target (connection.state.database.keys target table)
              table values (LiteralData.inserted table values) with
          | ok written =>
            obtain rfl := insertOutcome_ok outcome
            simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput, located,
              Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers,
              Connection.afterStep, Connection.afterWrite, LiteralData.insertCounts, same, Connection.resolveState]
            rfl
          | error failure =>
            obtain ⟨reason, reached⟩ := failure
            obtain ⟨rfl, kind⟩ := insertOutcome_error outcome
            rcases kind with rfl | rfl <;>
            · simp [SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed,
                StatementExecution.ofAlternatives, RunStep.withOthers, Connection.afterStep,
                Connection.afterError_failed, same, Connection.resolveState]
              rfl

end Belay.Sqlite.Model
