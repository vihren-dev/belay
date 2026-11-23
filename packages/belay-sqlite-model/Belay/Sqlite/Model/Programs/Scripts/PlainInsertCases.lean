import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule
import Belay.Sqlite.Model.Schema.Writes.PlainInsertFailure

set_option doc.verso true

/-! The case laws of plain INSERT: an INSERT of rows without a RETURNING clause and without write rules. Each case
law states one case of the kind rule {lit}`runScriptStep_plainInsert_eq` as a short theorem, and its proof uses
the kind rule and does not unfold the step function. A client selects a case with facts about the clock, the
counters, the table and the values, and gets the step as an equation. -/

namespace Belay.Sqlite.Model

/-- The success law of plain INSERT. For every resolution context, clock, index, connection, statement, parameter
values, resolution state, target position, rows of cells, subqueries, clock value and table: if the statement
resolves to an INSERT of the rows into the target with the subqueries, without a RETURNING clause and without write
rules, the statement has the clock value, no counter that it reads is unknown, the target holds the table, the
subqueries are plain, the cells are ready, and the values satisfy {name}`InsertFits`, then the step continues with
the output {lit}`.done rows.length` and with no further execution. Its connection is the connection after the write
({name}`Connection.afterWrite`) of the database that {name}`Database.setRows` gives for the target and the rows of
{name}`LiteralData.inserted`, with the counts of the insertion. The law does not say that the target has a row
list; when it has none, {name}`Database.setRows` gives the database before. Proof sketch: rewrite the step with
{name}`runScriptStep_plainInsert_eq`; the premises select the success case, with {name}`insertReady_of_fits` for
the readiness check and {name}`insertOutcome_of_fits` for the outcome. -/
theorem runScriptStep_insert_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query} {value : Int} {table : Table}
    (found : resolveStatement context connection.resolveState statement = .ok (.insert target rows [] subqueries none, after))
    (timed : statementClock clock index (.insert target rows [] subqueries none) = some value)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.insert target rows [] subqueries none).counterReads = none)
    (located : connection.state.database.table target = some table) (plain : Resolved.subqueriesPlain subqueries = true) :
    let resolved := Resolved.Statement.insert target rows [] subqueries none
    let counters := connection.state.counters.view resolved.counterReads
    let eval := Resolved.statementContext value counters parameters connection.state.database subqueries
    let values := Resolved.rowsAt eval table.shape.columns rows
    let written := connection.state.database.setRows target (LiteralData.inserted table values).rows
    let keys := connection.state.database.keys target table
    Resolved.cellsReady eval rows = true → InsertFits keys table values →
      runScriptStep context clock index connection statement parameters =
        .continued (.done rows.length) (connection.afterWrite written (LiteralData.insertCounts (.ok written) keys table values)) [] := by
  dsimp only
  intro ready fits
  rw [runScriptStep_plainInsert_eq found]
  simp only [timed, known, located]
  rw [insertReady_of_fits fits, plain, ready, insertOutcome_of_fits fits]
  rfl

/-- The failure law of plain INSERT. For every resolution context, clock, index, connection, statement, parameter
values, resolution state, target position, rows of cells, subqueries, clock value, table and reason: if the
statement resolves to an INSERT of the rows into the target with the subqueries, without a RETURNING clause and
without write rules, the statement has the clock value, no counter that it reads is unknown, the target holds the
table, the subqueries are plain, the cells are ready, the values pass the readiness check
({name}`LiteralData.insertReady`), and the outcome ({name}`insertOutcome`) is an error with the reason and the
database before, then the step continues with the error output of the primary code of the reason and with no
further execution. Its connection is the connection after the write ({name}`Connection.afterWrite`) of the database
before the statement, with the counts of the failed insertion. The premise loses no case: each error outcome has
the database before ({name}`insertOutcome_error`). {name}`LiteralData.insertCounts_error_changes` gives 0 changed
rows, and {name}`insertOutcome_constraintViolation` gives the outcome of rows that break a constraint. Proof sketch:
rewrite the step with {name}`runScriptStep_plainInsert_eq`; the premises select the failure case. -/
theorem runScriptStep_insert_failed {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query} {value : Int} {table : Table}
    {reason : ExecutionError}
    (found : resolveStatement context connection.resolveState statement = .ok (.insert target rows [] subqueries none, after))
    (timed : statementClock clock index (.insert target rows [] subqueries none) = some value)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.insert target rows [] subqueries none).counterReads = none)
    (located : connection.state.database.table target = some table) (plain : Resolved.subqueriesPlain subqueries = true) :
    let resolved := Resolved.Statement.insert target rows [] subqueries none
    let counters := connection.state.counters.view resolved.counterReads
    let eval := Resolved.statementContext value counters parameters connection.state.database subqueries
    let values := Resolved.rowsAt eval table.shape.columns rows
    let keys := connection.state.database.keys target table
    let result := LiteralData.inserted table values
    Resolved.cellsReady eval rows = true → LiteralData.insertReady keys table values result = true →
      insertOutcome connection.state.database target keys table values result = .error (reason, connection.state.database) →
      runScriptStep context clock index connection statement parameters =
        .continued (.error reason.primaryCode)
          (connection.afterWrite connection.state.database (LiteralData.insertCounts (.error (reason, connection.state.database)) keys table values)) [] := by
  dsimp only
  intro ready checked failed
  rw [runScriptStep_plainInsert_eq found]
  simp only [timed, known, located]
  rw [checked, plain, ready, failed]
  rfl

end Belay.Sqlite.Model
