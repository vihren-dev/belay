import Belay.Sqlite.ContextObservationLaws

set_option doc.verso true

/-!
When the real-context observation ({lit}`Script.outputIn`) equals the default observation. The
bridge covers a query statement that reads no clock and no counter, and that resolution turns into
the same query in both contexts over equal databases. It does not cover every read-only query.
-/

namespace Belay.Sqlite
open Model

/-- For every script that starts with a statement that resolution turns into a query at the
connection of the context, the real-context output is the output of that resolved statement at
the context's clock, next index and connection. Proof sketch: the first output of a run is
the output of its first step ({name}`runScriptFrom_head_cons`), which resolution determines
({name}`runScriptStep_output`). -/
theorem Script.outputIn_query (script : Script) (context : ExecutionContext) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (query : Resolved.Query) (subqueries : List Resolved.Query) (after : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext context.connection.resolveState statement =
      .ok (.query query subqueries, after)) :
    script.outputIn context = some (resolvedStepOutput context.clock context.index context.connection
      parameters (.query query subqueries)) := by
  unfold Script.outputIn
  rw [head, runScriptFrom_head_cons, runScriptStep_output, resolved]

/-- For every script that starts with a statement, and two contexts at which resolution gives
the same query, if the query reads no clock and no counter, and the two contexts see the same
database, then the two real-context outputs are equal. The contexts may differ in clock, index,
counters, settings, trace and open transaction, as far as these do not change the resolution.
This is not true for every read-only query: a clock read, a counter read or a pragma setting
can differ between the contexts. Proof sketch: both outputs unfold to the resolved statement's
output; a statement without a clock read takes the clock value 0 in every context, and then the
output of a query without counter reads depends only on the database
({name}`resolvedStepOutput_query`). -/
theorem Script.outputIn_eq_of_independent (script : Script) (first second : ExecutionContext)
    (statement : Syntax.Statement) (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (query : Resolved.Query) (subqueries : List Resolved.Query) (afterFirst afterSecond : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolvedFirst : resolveStatement runContext first.connection.resolveState statement =
      .ok (.query query subqueries, afterFirst))
    (resolvedSecond : resolveStatement runContext second.connection.resolveState statement =
      .ok (.query query subqueries, afterSecond))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (noCounters : (Resolved.Statement.query query subqueries).counterReads = [])
    (sameDatabase : first.connection.state.database = second.connection.state.database) :
    script.outputIn first = script.outputIn second := by
  have clockFree : ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      resolvedStepOutput clock index connection parameters (.query query subqueries) =
        resolvedStepOutput none index connection parameters (.query query subqueries) := by
    intro clock index connection
    simp [resolvedStepOutput, statementClock, noClock]
  rw [Script.outputIn_query script first statement parameters rest query subqueries afterFirst head resolvedFirst,
    Script.outputIn_query script second statement parameters rest query subqueries afterSecond head resolvedSecond,
    clockFree first.clock first.index first.connection, clockFree second.clock second.index second.connection,
    resolvedStepOutput_query first.index first.connection parameters query subqueries noClock
      (by simp [noCounters, Counters.firstUnknown]),
    resolvedStepOutput_query second.index second.connection parameters query subqueries noClock
      (by simp [noCounters, Counters.firstUnknown])]
  simp [noCounters, sameDatabase]

/-- For every query script, context and statement as in {name}`Script.outputIn_eq_of_independent`:
if resolution gives the same query at the context and at its default observation, and the query
reads no clock and no counter, then the real-context assertion equals the default assertion.
The two observations can still differ for another query on the same context. Proof sketch:
apply the output equality to the context and its default observation, which see the same database. -/
theorem Holds.inContext_iff_reached (script : Script) (context : ExecutionContext)
    (query : script.isQuery = true) (statement : Syntax.Statement) (parameters : List Value)
    (rest : List (Syntax.Statement × List Value)) (resolvedQuery : Resolved.Query)
    (subqueries : List Resolved.Query) (afterHere afterDefault : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (here : resolveStatement runContext context.connection.resolveState statement =
      .ok (.query resolvedQuery subqueries, afterHere))
    (byDefault : resolveStatement runContext context.defaultObservation.connection.resolveState statement =
      .ok (.query resolvedQuery subqueries, afterDefault))
    (noClock : (Resolved.Statement.query resolvedQuery subqueries).readsClock = false)
    (noCounters : (Resolved.Statement.query resolvedQuery subqueries).counterReads = []) :
    Holds.inContext script context query ↔ Holds.reached script context query := by
  unfold Holds.inContext Holds.reached Holds.inContext
  rw [Script.outputIn_eq_of_independent script context context.defaultObservation statement parameters rest
    resolvedQuery subqueries afterHere afterDefault head here byDefault noClock noCounters rfl]

end Belay.Sqlite
