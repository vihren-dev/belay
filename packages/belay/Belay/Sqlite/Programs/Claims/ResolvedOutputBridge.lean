import Belay.Sqlite.Programs.Claims.TwoStateAssertions
import Belay.Sqlite.Programs.Scripts.ContextObservationBridge

set_option doc.verso true

/-!
From an assertion on a query script to the output of its resolved statement. When the one statement of
a script resolves, {lit}`Holds.inContext` and {lit}`Holds.inContextSince` hold exactly when the output of
the resolved statement ({lit}`resolvedStepOutput`) has rows. The laws of the model about that output then
decide the assertion: the laws for a calm query, for {lit}`SELECT 1 WHERE c`, for {lit}`EXISTS` and for a
compound. The two-state law observes the statement with the initial database when the query names a
schema, and without it otherwise.
-/

namespace Belay.Sqlite
open Model

/-- For every script of one query statement with values, initial database and context: if the statement
resolves against the catalog of the initial database and the catalog of the context's database
({name}`resolveTwoState`), the two-state observation is the output of the resolved statement at the clock,
index and connection of the context. The initial database is given to that output exactly when the query
or a subquery names a schema ({name}`usesSchema`). Proof sketch: unfold the observation and substitute the
statement, its parts and the resolution. -/
theorem Script.observeTwoStateIn_resolved {script : Script} {statement : Syntax.Statement}
    {parameters : List Value} {query : Syntax.Subquery} {subqueries : List Syntax.Subquery}
    (initial : Database.Raw) (context : ExecutionContext) {resolved : Resolved.Statement} {after : Catalog}
    (single : script.statements = [(statement, parameters)]) (parts : statement.asQuery? = some (query, subqueries))
    (resolves : resolveTwoState runContext initial.catalog context.connection.state.database.catalog query
      subqueries = .ok (resolved, after)) :
    script.observeTwoStateIn initial context = resolvedStepOutput context.clock context.index context.connection
      parameters resolved (if usesSchema query subqueries then some initial else none) := by
  unfold Script.observeTwoStateIn Model.observeTwoState
  simp only [single, parts, resolves]

/-- For every script, initial database and context as in {name}`Script.observeTwoStateIn_resolved`: the
two-state assertion {name}`Holds.inContextSince` holds exactly when the output of the resolved statement, with
the initial database when the query names a schema, has rows. Proof sketch:
{name}`Script.observeTwoStateIn_resolved`. -/
theorem Holds.inContextSince_iff_hasRows {script : Script} {statement : Syntax.Statement}
    {parameters : List Value} {query : Syntax.Subquery} {subqueries : List Syntax.Subquery}
    (initial : Database) (context : ExecutionContext) {resolved : Resolved.Statement} {after : Catalog}
    (isQuery : script.isQuery = true)
    (single : script.statements = [(statement, parameters)]) (parts : statement.asQuery? = some (query, subqueries))
    (resolves : resolveTwoState runContext initial.raw.catalog context.connection.state.database.catalog query
      subqueries = .ok (resolved, after)) :
    Holds.inContextSince script initial context isQuery ↔
      (resolvedStepOutput context.clock context.index context.connection parameters resolved
        (if usesSchema query subqueries then some initial.raw else none)).hasRows = true := by
  unfold Holds.inContextSince
  rw [Script.observeTwoStateIn_resolved initial.raw context single parts resolves]

/-- For every script of one statement with values and every context: if the statement resolves in the
resolution state of the context's connection ({name}`resolveStatement`), the one-state assertion
{name}`Holds.inContext` holds exactly when the output of the resolved statement, without an initial database,
has rows. Proof sketch: {name}`Script.outputIn_resolved`. -/
theorem Holds.inContext_iff_hasRows {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (context : ExecutionContext) {resolved : Resolved.Statement} {after : ResolveState}
    (isQuery : script.isQuery = true) (single : script.statements = [(statement, parameters)])
    (resolves : resolveStatement runContext context.connection.resolveState statement = .ok (resolved, after)) :
    Holds.inContext script context isQuery ↔
      (resolvedStepOutput context.clock context.index context.connection parameters resolved).hasRows = true := by
  unfold Holds.inContext
  rw [Script.outputIn_resolved script context statement parameters [] resolved after single resolves]
  simp

end Belay.Sqlite
