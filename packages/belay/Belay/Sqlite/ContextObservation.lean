import Belay.Sqlite.ExecutionContext
import Belay.Sqlite.Queries

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- The output that a script gives when it runs from the supplied execution context: the
first output of the model's run from the context's clock, next statement index and connection
({name}`Belay.Sqlite.Model.runScriptFrom`). It reads the actual clock, counters, settings and
open transaction of the context. It executes nothing for the proof: the run is only observed,
so the context keeps its index, trace and connection. For a one-statement query, this is the
output of that statement; {lean}`(none : Option Output)` is the output of an empty script.
Use {name}`Script.outputOn` for the default observation of a database. -/
def Script.outputIn (script : Script) (context : ExecutionContext) : Option Output :=
  (runScriptFrom runContext context.clock context.index context.connection script.statements).outputs.head?

/-- The context in which {name}`Script.outputOn` observes a plain database: no clock, index zero,
the idle connection with unknown counters, foreign keys off, no open transaction and an empty
trace. -/
def Database.Raw.observationContext (raw : Database.Raw) : ExecutionContext :=
  ⟨none, 0, raw.connection, []⟩

/-- The context of the default observation of the database that a context sees: the database of the
connection, observed as {name}`Script.outputOn` observes a database. The clock, index, counters,
settings and open transaction of the original context do not take part. -/
def ExecutionContext.defaultObservation (context : ExecutionContext) : ExecutionContext :=
  Database.Raw.observationContext context.connection.state.database

/-- For every database, {name}`Script.outputOn` is the real-context observation at the default
observation context of the plain database. Proof sketch: both unfold to the head output of the
run from the idle connection; the definitions agree by computation. -/
theorem Script.outputOn_eq_outputIn (script : Script) (db : Database) :
    script.outputOn db = script.outputIn db.raw.observationContext := rfl

/-- The real-context assertion: the single read-only query gives at least one row, for every
result that SQLite may give for it, when it runs from the supplied context. In terms of the
formula, the output of the query at the context ({name}`Script.outputIn`) is {name}`Output.rows`
with at least one row, or {name}`Output.oneOf` with at least one result and a row in each result.
It uses the actual clock at the context's next statement index, the actual counters, the settings
and the open transaction. It does not hold when the output is empty, an error or unmodeled, for
example for a clock read in a context without a clock. It runs no step of the program: the
context keeps its index and trace. Use {lit}`Holds.reached` for the default observation. -/
def Holds.inContext (script : Script) (context : ExecutionContext)
    (_query : script.isQuery = true := by check_query) : Prop :=
  (script.outputIn context).any Output.hasRows = true

instance (script : Script) (context : ExecutionContext) (query : script.isQuery = true) :
    Decidable (Holds.inContext script context query) :=
  inferInstanceAs (Decidable (_ = true))

/-- The default assertion at a context: {name}`Holds` of the query, observed on the database that
the context's connection sees. It uses the default observation of that database
({name}`ExecutionContext.defaultObservation`): no clock, unknown counters, foreign keys off and no
open transaction, whatever the context has. So it does not state a fact about the actual clock,
counters or settings, and it does not require a fresh run. For example, it holds in a context
whose open transaction has inserted the row that the query needs. -/
def Holds.reached (script : Script) (context : ExecutionContext)
    (query : script.isQuery = true := by check_query) : Prop :=
  Holds.inContext script context.defaultObservation query

instance (script : Script) (context : ExecutionContext) (query : script.isQuery = true) :
    Decidable (Holds.reached script context query) :=
  inferInstanceAs (Decidable (_ = true))

end Belay.Sqlite
