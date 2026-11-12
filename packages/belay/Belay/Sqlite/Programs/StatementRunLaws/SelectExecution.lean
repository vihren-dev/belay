import Belay.Sqlite.Programs.Scripts.RunResultSteps

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every script of one statement with its values, database, environment, property {lit}`Q`
of a result and property {lit}`E` of a result code: when the statement resolves to a query
statement on the new connection, the step runs it at a clock value with known counters and source
rows {lit}`source`, and a nested subquery has a fallible call, the source possibly fails, or the
run possibly fails, then the run of the script returns neither a result with {lit}`Q` nor an error
with {lit}`E`. Proof sketch: {name}`resolvedStepOutput_select_unready` gives an unmodeled output,
which returns neither. -/
theorem Run.send_unready {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (db : Database) (env : Env) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (clocked : statementClock env.clock 0 (.query query subqueries) = some value)
    (known : (db.raw.connection env.counters).state.counters.firstUnknown
      (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      (db.raw.connection env.counters).state.database = some source)
    (unready : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = false ∨ source.fault = .may ∨
      (query.run ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
        source.rows).fault = .may)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run script env).returnsResult property ∧ ¬ (db.run script env).returnsError code := by
  have one : script.statements.length = 1 := by rw [head]; rfl
  rw [Run.send_returnsResult_iff one, Run.send_returnsError_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same, runScriptStep_output, resolved]
  dsimp only
  rw [resolvedStepOutput_select_unready env.clock 0 _ parameters clocked known found unready]
  simp [Output.returnsResult, Output.returnsError]

/-- Failure rule of a run: for every script of one statement with its values, database,
environment, property {lit}`Q` of a result and property {lit}`E` of a result code: when the
statement resolves to a query statement that is no compound on the new connection, the step runs
it at a clock value with known counters, source rows {lit}`source` and a window that binds to the
query {lit}`bound`, no nested subquery has a fallible call, the source does not possibly fail, and
{lit}`bound` over the source rows has no failing aggregate and certainly fails
({name}`Resolved.Query.mustFail`), then

* the run of the script returns no result with {lit}`Q`, and
* it returns an error with {lit}`E` exactly when {lit}`E` holds of the primary code of a failing
  function.

Proof sketch: {name}`resolvedStepOutput_select_mustFail` gives the error output. -/
theorem Run.send_mustFail {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (db : Database) (env : Env) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (single : query.compound = none)
    (clocked : statementClock env.clock 0 (.query query subqueries) = some value)
    (known : (db.raw.connection env.counters).state.counters.firstUnknown
      (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      (db.raw.connection env.counters).state.database = some source)
    (plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true)
    (sourceCertain : source.fault ≠ .may)
    (window : query.bindWindow parameters = some bound)
    (noOverflow : bound.fails ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      source.rows = false)
    (mustFail : bound.mustFail ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      source.rows = true)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run script env).returnsResult property ∧
      ((db.run script env).returnsError code ↔ code ExecutionError.functionError.primaryCode) := by
  have one : script.statements.length = 1 := by rw [head]; rfl
  rw [Run.send_returnsResult_iff one, Run.send_returnsError_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same, runScriptStep_output, resolved]
  dsimp only
  rw [resolvedStepOutput_select_mustFail env.clock 0 _ parameters single clocked known found plain sourceCertain window
    noOverflow mustFail]
  simp [Output.returnsResult, Output.returnsError]

/-- Prepare-error rule: for every script of one statement with its values, proof that it has one
statement, database, environment, property {lit}`Q` of a result and property {lit}`E` of a result
code: when the statement resolves on the connection of the environment to a prepare error
({name}`resolveStatement`), then

* the run of the program {name}`query` of the script returns no result with {lit}`Q`
  ({name}`Run.returnsResult`), and
* it returns an error with {lit}`E` ({name}`Run.returnsError`) exactly when {lit}`E` holds of the
  primary code of that prepare error ({name}`ExecutionError.primaryCode`).

The rule holds for every environment: the statement reads no clock and no counter. Proof sketch:
{name}`runScriptStep_output` reads the resolution, and {name}`resolvedStepOutput_prepareError`
gives the error output. -/
theorem Run.query_prepareError {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {error : PrepareError} {after : ResolveState}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.prepareError error, after))
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (Belay.Sqlite.query script one) env).returnsResult property ∧
      ((db.run (Belay.Sqlite.query script one) env).returnsError code ↔
        code (ExecutionError.prepare error).primaryCode) := by
  rw [Run.query_returnsResult_iff one, Run.query_returnsError_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same, runScriptStep_output, resolved]
  dsimp only
  rw [resolvedStepOutput_prepareError]
  simp [Output.returnsResult, Output.returnsError]

end Belay.Sqlite
