import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- If a statement resolves to a plain INSERT without RETURNING or write rules, its clock and counters
are known, its target exists, its subqueries are plain, its cell expressions are ready and the values
satisfy {name}`InsertFits`, the step continues once with the inserted row count. Its next connection
publishes the inserted rows and applies the insertion counts. Proof sketch: the kind rule
{name}`runScriptStep_plainInsert_eq` with {name}`insertReady_of_fits` and {name}`insertOutcome_of_fits`. -/
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
  rw [runScriptStep_plainInsert_eq found]
  simp (config := { zetaDelta := true }) only [timed, known, located, insertReady_of_fits fits, plain, cells,
    insertOutcome_of_fits fits, Bool.and_self, ite_true]
  done

end Belay.Sqlite.Model
