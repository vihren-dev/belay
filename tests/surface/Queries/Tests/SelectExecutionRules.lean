import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Checks of the execution rule of ADR 0027 D5 ({lit}`Run.send_returnsResult_select`) and of its
unready contrast ({lit}`Run.send_unready`, acceptance case B05). The rule holds for every database
and environment: a calm query of one table returns a result with a property exactly when every
result that the model permits over the scan of the table has it. A possible fault blocks every claim,
also when the output of the query alone ({lit}`Resolved.Query.outputOn`) gives a result. -/

namespace SelectExecutionRules
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- For every script of one statement, database, environment and property {lit}`Q`: when the
statement resolves on the connection of the environment to a calm query of one table at a catalog
position, with no subqueries, no compound and no window parameter, no failing aggregate and a
certain {lit}`DISTINCT` over the scan of the table, the run returns a result with {lit}`Q` exactly
when every result that the model permits over the scan has {lit}`Q`. The environment's clock and
counters do not matter, because the statement reads neither. -/
theorem calm_table (script : Script) (db : Database) (env : Env) {statement : Syntax.Statement}
    {parameters : List Value} {query : Resolved.Query} {after : ResolveState} {position : Nat} {table : Table}
    (head : script.statements = [(statement, parameters)])
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (sources : query.sources = [.first position])
    (present : (db.raw.connection env.counters).state.database.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) :
    (db.run script env).returnsResult property ↔
      ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        property result := by
  have ready := Connection.SelectReady.of_calm (db.raw.connection env.counters) parameters calm single
    limitParameter offsetParameter (Resolved.Query.source_first _ query _ position table sources present)
    (by simp) noOverflow distinct
  have context : (db.raw.connection env.counters).queryContextAt 0 parameters query [] =
      Resolved.EvalContext.bound parameters :=
    Connection.queryContext_of_quiet _ parameters query calm.quiet
  rw [Run.send_returnsResult_select head db env resolved (by simp [statementClock, calm.readsClock]) ready property,
    context]

/-- One row whose absolute value overflows, so that the call {lit}`abs(value)` may fail. -/
def extreme : Database := db! r"
  CREATE TABLE items(value INTEGER NOT NULL);
  INSERT INTO items VALUES (-9223372036854775808);"

/-- One row whose absolute value is 1. -/
def calmRow : Database := db! r"
  CREATE TABLE items(value INTEGER NOT NULL);
  INSERT INTO items VALUES (-1);"

/-- A filter with a call that may fail on a row. -/
def possibleFault : Script := sql r"SELECT 1 FROM items WHERE abs(value) = 1"

/-- The output of the query of the first statement of a script on a database, at the clock value 0
with no values ({name}`Resolved.Query.outputOn`), without the readiness check of the step; none for a
statement that does not resolve to a query. -/
def queryOutput (db : Database) (script : Script) : Option Output :=
  match script.statements with
  | (statement, _) :: _ => match resolveStatement runContext db.raw.connection.resolveState statement with
    | .ok (.query query subqueries, _) => some (query.outputOn 0
        (db.raw.connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) []
        db.raw.connection.state.database subqueries)
    | _ => none
  | [] => none

/-- B05: the output of the query alone has no row, an empty successful result, but the call of the
filter may fail on the row, so the run returns neither a result nor an error, not even with the
property {lean}`fun (_ : List (List Value)) => True`. -/
theorem possible_fault_blocks_success :
    (queryOutput extreme possibleFault).any Output.hasNoRows = true ∧
      ¬ (extreme.run possibleFault).returnsResult (fun _ => True) ∧
      ¬ (extreme.run possibleFault).returnsError (fun _ => True) := by
  decide +kernel

/-- B05 contrast: on a row where the call cannot fail, the same query returns its row. -/
theorem calm_row_returns :
    (calmRow.run possibleFault).returnsResult (· = [[.integer 1]]) := by
  decide +kernel

#print axioms calm_table
#print axioms possible_fault_blocks_success
#print axioms calm_row_returns

end SelectExecutionRules
