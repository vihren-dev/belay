import Belay.Sqlite.SelectExecution

set_option doc.verso true

/-! The execution rules of a calm SELECT (ADR 0027, D5): a script of one SELECT statement whose
expressions have no fallible call and read no clock and no counter
({lit}`Belay.Sqlite.Model.Resolved.Statement.Calm`) returns a result with a property exactly when
every result that the model permits for its query in the statement context has the property. The
statement context has the values and the runs of the subqueries, and no clock or counter, so the
rules hold for every environment. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Faultless rule: for every script of one statement with its values, proof that it has one
statement, database, environment, source rows {lit}`source`, query {lit}`bound` and property
{lit}`Q` of a result: when the statement resolves on the connection of the environment to a calm
query ({name}`Resolved.Statement.Calm`) with subqueries, the query's sources give {lit}`source` over
the database in the statement context ({name}`Resolved.EvalContext.statement`), {lit}`source` has
no possible fault, the query is no compound and its window binds to {lit}`bound` with the values
({name}`Resolved.Query.bindWindow`), each expression of the query has no fault in the statement
context over the empty row and over each source row, and {lit}`bound` has no overflow
({lit}`Query.fails`) and a certain {lit}`DISTINCT` over the source rows, then the run of the program
{name}`query` of the script returns a result with {lit}`Q` exactly when every result that the model
permits for {lit}`bound` over the source rows in the statement context has {lit}`Q`. The clock and
the counters of the environment do not matter. Proof sketch:
{name}`Connection.SelectReady.of_faultless` gives the readiness premises,
{name}`Connection.queryContext_calm` the context, and {name}`Run.query_returnsResult_select` the
equivalence. -/
theorem Run.query_returnsResult_faultless {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query bound : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (found : query.source (Resolved.EvalContext.statement parameters db.raw subqueries) db.raw = some source)
    (sourceCertain : source.fault ≠ .may)
    (calm : (Resolved.Statement.query query subqueries).Calm) (single : query.compound = none)
    (window : query.bindWindow parameters = some bound)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (Resolved.EvalContext.statement parameters db.raw subqueries) row).2 = .none)
    (noOverflow : bound.fails (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows = false)
    (distinct : bound.distinctCertain (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ bound.possibleResults (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows,
        property result := by
  have ready := Connection.SelectReady.of_faultless (db.raw.connection env.counters) parameters calm single window
    found sourceCertain faultless noOverflow distinct
  have context : (db.raw.connection env.counters).queryContextAt 0 parameters query subqueries =
      Resolved.EvalContext.statement parameters db.raw subqueries :=
    Connection.queryContext_calm _ parameters query subqueries calm
  rw [Run.query_returnsResult_select head one db env resolved (by simp [statementClock, calm.readsClock]) ready
    property, context]

/-- Compound rule: for every script of one statement with its values, proof that it has one
statement, database, environment, source rows {lit}`source`, query {lit}`bound` and property
{lit}`Q` of a result: when the statement resolves on the connection of the environment to a calm
query ({name}`Resolved.Statement.Calm`) that is the compound {lit}`compound`, with subqueries, the
query's sources give {lit}`source` over the database in the statement context
({name}`Resolved.EvalContext.statement`), {lit}`source` has no possible fault, the window binds to
{lit}`bound`, the run of each term ({name}`Resolved.Compound.terms`) in the statement context for
the first source row ends with {lean}`Resolved.RunEnd.done`, and each operator keeps certain rows
({name}`Resolved.Compound.combined`), then the run of the program {name}`query` of the script returns
a result with {lit}`Q` exactly when every result that the model permits for {lit}`bound` over the
source rows in the statement context has {lit}`Q`. The clock and the counters of the environment do
not matter. Proof sketch: {name}`Connection.SelectReady.of_compound` and
{name}`Run.query_returnsResult_select`. -/
theorem Run.query_returnsResult_compound {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query bound : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows} {compound : Resolved.Compound}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (calm : (Resolved.Statement.query query subqueries).Calm) (shape : query.compound = some compound)
    (found : query.source (Resolved.EvalContext.statement parameters db.raw subqueries) db.raw = some source)
    (sourceCertain : source.fault ≠ .may) (window : query.bindWindow parameters = some bound)
    (done : ∀ index ∈ compound.terms,
      ((Resolved.EvalContext.statement parameters db.raw subqueries).subqueries index (source.rows.headD [])).ending =
        .done)
    (certain : (compound.combined (Resolved.EvalContext.statement parameters db.raw subqueries)
      (source.rows.headD [])).2 = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ bound.possibleResults (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows,
        property result := by
  have ready := Connection.SelectReady.of_compound (db.raw.connection env.counters) parameters calm shape found
    sourceCertain window done certain
  have context : (db.raw.connection env.counters).queryContextAt 0 parameters query subqueries =
      Resolved.EvalContext.statement parameters db.raw subqueries :=
    Connection.queryContext_calm _ parameters query subqueries calm
  rw [Run.query_returnsResult_select head one db env resolved (by simp [statementClock, calm.readsClock]) ready
    property, context]

/-- Calm rule: for every script of one statement with its values, proof that it has one statement,
database, environment, source rows {lit}`source` and property {lit}`Q` of a result: when the
statement resolves on the connection of the environment to a calm query
({name}`Resolved.Statement.Calm`) with no subqueries, the query's sources give {lit}`source` over the
database with only the values as context, {lit}`source` has no possible fault, and the query is no
compound and has no window parameter, no overflow ({lit}`Query.fails`) and a certain
{lit}`DISTINCT` over the source rows, then the run of the program {name}`query` of the script
returns a result with {lit}`Q` exactly when every result that the model permits over the source
rows has {lit}`Q`. The context has only the values ({name}`Resolved.EvalContext.bound`): the clock
and the counters of the environment do not matter. Proof sketch:
{name}`Run.query_returnsResult_faultless`; calm expressions have no fault in the context of the
values ({name}`Resolved.Statement.Calm.faultless_nil`). -/
theorem Run.query_returnsResult_calm {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {after : ResolveState} {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (found : query.source (Resolved.EvalContext.bound parameters) db.raw = some source)
    (sourceCertain : source.fault ≠ .may)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) source.rows = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) source.rows = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) source.rows, property result := by
  have faultless := calm.faultless_nil (db.raw.connection env.counters) parameters (rows := source.rows)
  rw [Connection.queryContext_calm _ parameters query [] calm] at faultless
  exact Run.query_returnsResult_faultless head one db env resolved found sourceCertain calm single
    (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter) faultless noOverflow distinct
    property

/-- Calm one-table rule: {name}`Run.query_returnsResult_calm` for a query whose sources are the
first source at a catalog position where the database has a table: for every script of one
statement with its values, database, environment and property {lit}`Q` of a result, under the same
premises over the scan of the table ({name}`Resolved.sourceRows`), the run of the program
{name}`query` of the script returns a result with {lit}`Q` exactly when every result that the model
permits over the scan has {lit}`Q`. Proof sketch: {name}`Resolved.Query.source_first` gives the
source rows. -/
theorem Run.query_returnsResult_calmTable {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {after : ResolveState} {position : Nat} {table : Table}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (sources : query.sources = [.first position]) (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        property result :=
  Run.query_returnsResult_calm head one db env resolved
    (Resolved.Query.source_first _ query _ position table sources present) (by simp) calm single limitParameter
    offsetParameter noOverflow distinct property

end Belay.Sqlite
