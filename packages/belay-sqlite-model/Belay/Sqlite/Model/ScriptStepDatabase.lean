import Belay.Sqlite.Model.SuccessfulScriptEffects

set_option doc.verso true

/-! The connection after a successful ordinary statement. A statement that is not a transaction
control changes the database and the counters of its connection and nothing else, so a law that names
the next database names the whole next connection. -/

namespace Belay.Sqlite.Model

/-- For every connection, statement that resolves to an ordinary resolved statement (not a transaction
control), error-free step that continues, and database that is the next database: the next connection is
the connection with that database and some counters. In plain words, the clock, the snapshot and both
connection settings stay as they were. Proof sketch: {name}`runScriptStep_effect` gives the next
connection with the database of the effect; the premise identifies that database. -/
theorem runScriptStep_next_of_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} {database : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) (stored : next.state.database = database) :
    ∃ counters, next = { connection with state := { connection.state with database, counters } } := by
  obtain ⟨value, effect, -, -, nextEq⟩ := runScriptStep_effect found ordinary step noError
  rw [nextEq] at stored
  exact ⟨_, by rw [nextEq, ← stored]⟩

end Belay.Sqlite.Model
