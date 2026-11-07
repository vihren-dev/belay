import Belay.Sqlite.SelectExecution

set_option doc.verso true

/-! The overflow rule of a SELECT for the run of a script (ADR 0027, D5): a script of one SELECT
over one table whose aggregate overflows ({lit}`Belay.Sqlite.Model.Resolved.Query.fails`) returns
the error {lit}`integer overflow` and no result, in every environment. The value rules of an
aggregate do not hide the overflow: they give a value only under a premise that it does not
overflow. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Calm one-table overflow rule: for every script of one statement with its values, proof that it
has one statement, database, environment, property {lit}`Q` of a result and property {lit}`E` of
a result code: when the statement resolves on the connection of the environment to a calm query
({name}`Resolved.Statement.Calm`) with no subqueries, whose sources are the first source at a
catalog position where the database has a table, and which is no compound, has no window
parameter, a failing aggregate ({name}`Resolved.Query.fails`) and a certain {lit}`DISTINCT` over the scan
of the table ({name}`Resolved.sourceRows`), then

* the run of the program {name}`query` of the script returns no result with {lit}`Q`, and
* it returns an error with {lit}`E` exactly when {lit}`E` holds of the primary code of
  {name}`ExecutionError.integerOverflow`.

Proof sketch: the readiness premises of {name}`Connection.SelectReady.of_calm` without the
overflow give {name}`resolvedStepOutput_select_overflow`, an error output. -/
theorem Run.query_overflow_calmTable {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {after : ResolveState} {position : Nat} {table : Table}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (sources : query.sources = [.first position]) (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (overflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (Belay.Sqlite.query script one) env).returnsResult property ∧
      ((db.run (Belay.Sqlite.query script one) env).returnsError code ↔
        code ExecutionError.integerOverflow.primaryCode) := by
  have context : (db.raw.connection env.counters).queryContextAt 0 parameters query [] =
      Resolved.EvalContext.bound parameters := Connection.queryContext_of_calm _ parameters query calm
  have faultless := calm.faultless_nil (db.raw.connection env.counters) parameters (rows := Resolved.sourceRows table)
  rw [Run.query_returnsResult_iff one, Run.query_returnsError_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same, runScriptStep_output, resolved]
  dsimp only
  rw [resolvedStepOutput_select_overflow env.clock 0 _ parameters (value := 0) (by simp [statementClock, calm.readsClock]) single
    (calm.firstUnknown _) (by rw [context]; exact Resolved.Query.source_first _ query _ position table sources present)
    calm.subqueries_plain (by simp) (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter)
    (by rw [context]; exact overflow) (Resolved.Query.mustFail_of_faultless _ query _ faultless)
    (Resolved.Query.mayFail_of_faultless _ query _ calm.query_plain faultless) (by rw [context]; exact distinct)]
  simp [Output.returnsResult, Output.returnsError]

end Belay.Sqlite
