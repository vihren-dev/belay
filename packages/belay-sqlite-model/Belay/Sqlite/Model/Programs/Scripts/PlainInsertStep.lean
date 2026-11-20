import Belay.Sqlite.Model.Schema.Writes.PlainInsertSuccess
import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- If a statement resolves to a plain INSERT without RETURNING or write rules, its clock and counters
are known, its target exists, its subqueries are plain, its cell expressions are ready and the values
satisfy {name}`InsertFits`, the step continues once with the inserted row count. Its next connection
publishes the inserted rows and applies the insertion counts. Proof sketch: {name}`runStatement_insert_ok`
determines the run. Ordinary statements publish its database and counters and keep the connection settings. -/
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
  intro resolved counters eval values written keys cells fits
  obtain ⟨certified, counted⟩ := runStatement_insert_ok value counters parameters _ target table rows subqueries located plain cells fits
  let counts := LiteralData.insertCounts (.ok written) keys table values
  have ran : connection.state.statementRun value parameters resolved = { effect := .ok written, ready := true, counts } := by
    simp only [SqlState.statementRun, ← show counters = connection.state.counters.view resolved.counterReads from rfl]
    rw [show runStatement value counters parameters resolved connection.state.database = _ from certified, known]
    rfl
  have changes : counts.changes = some rows.length := by rw [certified] at counted; exact counted
  have ordinary : resolved.isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement resolved found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  dsimp only [resolved] at ran ordinary
  simp only [runScriptStep, runScriptStepWith, found, timed, known, ran, Bool.not_true, Bool.false_eq_true, ite_false,
    ranScriptStep, advanceRun_ordinary index (.insert target rows [] subqueries none) connection.state _ ordinary, SqlState.publish, SqlTransition.counted]
  simp [resolved, Output.ofStep, statementOutput, located, haltError, Resolved.Statement.returnsRows, changes,
    StatementExecution.ofAlternatives, Connection.afterStep, Connection.afterWrite, RunStep.withOthers, same,
    Connection.resolveState]
  rfl

end Belay.Sqlite.Model
