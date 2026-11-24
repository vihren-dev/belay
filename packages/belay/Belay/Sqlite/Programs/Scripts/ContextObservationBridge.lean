import Belay.Sqlite.Programs.Claims.ContextObservationLaws

set_option doc.verso true

/-!
When the real-context observation ({lit}`Script.outputIn`) equals the default observation. The
bridge covers a query statement that reads no clock and no counter, and that resolution turns into
the same query in both contexts over equal databases. It does not cover every read-only query.
-/

namespace Belay.Sqlite
open Model

/-- For a script beginning with a successfully resolved statement of any kind, its observed
output is the resolved statement's output on the observation connection, at its clock and
index. Proof sketch: take the first step output and substitute the resolution. -/
theorem Script.outputIn_resolved (script : Script) (context : ExecutionContext) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (kind : Resolved.Statement) (after : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext context.connection.resolveState statement =
      .ok (kind, after)) :
    script.outputIn context = some (resolvedStepOutput context.clock context.index context.connection
      parameters kind) := by
  unfold Script.outputIn
  rw [head, runScriptFrom_head_cons, runScriptStep_output, resolved]

/-- For every script and two contexts at which the script has the output of the same query, if the query reads no clock and no counter, and the two contexts see the same
database, then the two real-context outputs are equal. The contexts may differ in clock, index,
counters, settings, trace and open transaction, subject to the two output equations.
This is not true for every read-only query: a clock read, a counter read or a pragma setting
can differ between the contexts. Proof sketch: both outputs unfold to the resolved statement's
output; a statement without a clock read takes the clock value 0 in every context, and then the
output of a query without counter reads depends only on the database
({name}`resolvedStepOutput_query`). -/
theorem Script.outputIn_eq_of_independent (script : Script) (first second : ExecutionContext)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query)
    (firstOutput : script.outputIn first = some (resolvedStepOutput first.clock first.index first.connection
      parameters (.query query subqueries)))
    (secondOutput : script.outputIn second = some (resolvedStepOutput second.clock second.index second.connection
      parameters (.query query subqueries)))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (noCounters : (Resolved.Statement.query query subqueries).counterReads = [])
    (sameDatabase : first.connection.state.database = second.connection.state.database) :
    script.outputIn first = script.outputIn second := by
  have clockFree : ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      resolvedStepOutput clock index connection parameters (.query query subqueries) =
        resolvedStepOutput none index connection parameters (.query query subqueries) := by
    intro clock index connection
    simp [resolvedStepOutput, statementClock, noClock]
  rw [firstOutput, secondOutput,
    clockFree first.clock first.index first.connection, clockFree second.clock second.index second.connection,
    resolvedStepOutput_query first.index first.connection parameters query subqueries noClock
      (by simp [noCounters, Counters.firstUnknown]),
    resolvedStepOutput_query second.index second.connection parameters query subqueries noClock
      (by simp [noCounters, Counters.firstUnknown])]
  simp [noCounters, sameDatabase]

/-- For every query script and context as in {name}`Script.outputIn_eq_of_independent`:
if both observed outputs equal the output of the same query at their connections, and the query
reads no clock and no counter, then the real-context assertion equals the default assertion.
The two observations can still differ for another query on the same context. Proof sketch:
apply the output equality to the context and its default observation, which see the same database. -/
theorem Holds.inContext_iff_reached (script : Script) (context : ExecutionContext)
    (query : script.isQuery = true) (parameters : List Value) (resolvedQuery : Resolved.Query) (subqueries : List Resolved.Query)
    (here : script.outputIn context = some (resolvedStepOutput context.clock context.index context.connection
      parameters (.query resolvedQuery subqueries)))
    (byDefault : script.outputIn context.defaultObservation = some (resolvedStepOutput context.defaultObservation.clock
      context.defaultObservation.index context.defaultObservation.connection parameters (.query resolvedQuery subqueries)))
    (noClock : (Resolved.Statement.query resolvedQuery subqueries).readsClock = false)
    (noCounters : (Resolved.Statement.query resolvedQuery subqueries).counterReads = []) :
    Holds.inContext script context query ↔ Holds.reached script context query := by
  unfold Holds.inContext Holds.reached Holds.inContext
  rw [Script.outputIn_eq_of_independent script context context.defaultObservation parameters
    resolvedQuery subqueries here byDefault noClock noCounters rfl]

end Belay.Sqlite
