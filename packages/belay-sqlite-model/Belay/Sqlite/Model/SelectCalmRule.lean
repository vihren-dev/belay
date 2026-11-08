import Belay.Sqlite.Model.SelectRunRule
import Belay.Sqlite.Model.StatementQuiet
import Belay.Sqlite.Model.QueryPlainLaws
import Belay.Sqlite.Model.QueryStatementOutput

set_option doc.verso true

/-! The readiness of a calm query statement (ADR 0027, D5): a statement whose expressions have no
fallible call and read no clock and no counter ({lit}`Resolved.Statement.Calm`) evaluates in the
statement context of its values and subqueries ({lit}`Resolved.EvalContext.statement`), which is
the context of its values alone when it has no subqueries. Without subqueries its expressions have
no fault, and it is ready ({lit}`Connection.SelectReady`) when its source does not possibly fail,
it does not overflow, and its {lit}`DISTINCT` is certain. With subqueries it is ready under an
explicit premise that its expressions have no fault, when its window binds to the values. -/

namespace Belay.Sqlite.Model

/-- The context in which a calm statement without subqueries evaluates its expressions: the clock
value 0, no counter, and the values bound to its parameters. -/
abbrev Resolved.EvalContext.bound (parameters : List Value) : Resolved.EvalContext :=
  { Resolved.EvalContext.plain 0 with parameters }

/-- For every list of values, the values bound to the parameters of the context of the values are the values. Proof
sketch: the definition computes. -/
theorem Resolved.EvalContext.bound_parameters (parameters : List Value) :
    (Resolved.EvalContext.bound parameters).parameters = parameters := rfl

/-- For every connection, values and quiet statement of a query without subqueries
({name}`Resolved.Statement.Quiet`), the context of the query on the connection is the context of
the values ({name}`Resolved.EvalContext.bound`): the statement reads no counter, so the context
knows none. A calm statement is quiet ({name}`Resolved.Statement.Calm.quiet`); a quiet statement
can call a function that fails, such as {lit}`abs`. Proof sketch: the statement reads no counters
({name}`Resolved.Statement.Quiet.counterReads`), and the view of the counters for no read is no
counter. -/
theorem Connection.queryContext_of_quiet (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (quiet : (Resolved.Statement.query query []).Quiet) :
    connection.queryContext parameters query [] = Resolved.EvalContext.bound parameters := by
  simp only [Connection.queryContext, quiet.counterReads, Resolved.statementContext_nil]
  rfl

/-- The context in which a calm query statement evaluates its query and its subqueries: the
clock value 0, no counter, the values bound to its parameters, and the runs of its subqueries over
the database ({name}`Resolved.statementContext`). Without subqueries it is the context of the values
({name}`Resolved.EvalContext.bound`). -/
abbrev Resolved.EvalContext.statement (parameters : List Value) (database : Database)
    (subqueries : List Resolved.Query) : Resolved.EvalContext :=
  Resolved.statementContext 0 {} parameters database subqueries

/-- For every connection, values, query, subqueries and calm statement of the query with the
subqueries, the context of the query on the connection is the statement context of the values
over the database of the connection ({name}`Resolved.EvalContext.statement`): the statement reads no
counter, so the context knows none. Proof sketch: the statement reads no counters
({name}`Resolved.Statement.Calm.counterReads`), and the view of the counters for no read is no counter. -/
theorem Connection.queryContext_calm (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) (calm : (Resolved.Statement.query query subqueries).Calm) :
    connection.queryContext parameters query subqueries =
      Resolved.EvalContext.statement parameters connection.state.database subqueries := by
  simp only [Connection.queryContext, Connection.queryContextAt, calm.counterReads, Counters.view_nil]

/-- For every connection, values and calm statement of a query without subqueries, every expression of the
query has no fault over any row in the context of the query on the connection. Proof sketch: the context is
quiet ({name}`Resolved.EvalContext.plain_quiet`) and the expression has no fallible call
({name}`Resolved.Expr.fault_of_plain`). -/
theorem Resolved.Statement.Calm.faultless_nil {query : Resolved.Query} (calm : (Resolved.Statement.query query []).Calm)
    (connection : Connection) (parameters : List Value) :
    ∀ {rows : List (List Value)}, ∀ row ∈ [] :: rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query []) row).2 = .none := by
  intro rows row _ expression member
  have plain := calm.query_plain
  simp only [List.all_eq_true, Bool.not_eq_true'] at plain
  rw [Connection.queryContext_of_quiet connection parameters query calm.quiet]
  exact Resolved.Expr.fault_of_plain _ (fun _ _ => ⟨rfl, rfl, rfl⟩) row expression (plain expression member)

/-- Faultless rule: for every connection, values, calm statement of a query with subqueries, where
the query is no compound and its window binds to the query {lit}`bound` with the values
({name}`Resolved.Query.bindWindow`): when its source rows {lit}`source` in the statement context
({name}`Resolved.EvalContext.statement`) do not possibly fail, each expression of the query has no
fault in that context over the empty row and over each source row, {lit}`bound` has no failing
aggregate over them ({name}`Resolved.Query.fails`), and its {lit}`DISTINCT` is certain over them
({name}`Resolved.Query.distinctCertain`), the statement is ready at the clock value 0 with
{lit}`bound` as the bound query ({name}`Connection.SelectReady`). For a query without a window
parameter, {lit}`bound` is the query ({name}`Resolved.Query.bindWindow_literal`). The subqueries
are free: the premise on the expressions is what the query needs of them. Proof sketch:
{name}`Connection.SelectReady.of_phases`; the context is the statement context
({name}`Connection.queryContext_calm`), {lit}`bound` has the expressions of the query
({name}`Resolved.Query.bindWindow_some`), and expressions without a fault give no certain or
possible failure ({name}`Resolved.Query.mustFail_of_faultless`,
{name}`Resolved.Query.mayFail_of_faultless`). -/
theorem Connection.SelectReady.of_faultless (connection : Connection) (parameters : List Value)
    {query bound : Resolved.Query} {subqueries : List Resolved.Query} {source : Resolved.SourceRows}
    (calm : (Resolved.Statement.query query subqueries).Calm)
    (single : query.compound = none) (window : query.bindWindow parameters = some bound)
    (found : query.source (Resolved.EvalContext.statement parameters connection.state.database subqueries)
      connection.state.database = some source)
    (sourceCertain : source.fault ≠ .may)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (Resolved.EvalContext.statement parameters connection.state.database subqueries) row).2 =
        .none)
    (noOverflow : bound.fails (Resolved.EvalContext.statement parameters connection.state.database subqueries)
      source.rows = false)
    (distinct : bound.distinctCertain (Resolved.EvalContext.statement parameters connection.state.database subqueries)
      source.rows = true) :
    connection.SelectReady 0 parameters query subqueries source bound := by
  have context : connection.queryContextAt 0 parameters query subqueries =
      Resolved.EvalContext.statement parameters connection.state.database subqueries :=
    Connection.queryContext_calm connection parameters query subqueries calm
  obtain ⟨limit, offset, shape⟩ := Resolved.Query.bindWindow_some parameters query bound window
  have expressions : bound.expressions = query.expressions := by rw [shape]; rfl
  have plain := calm.query_plain
  rw [← expressions] at faultless plain
  refine Connection.SelectReady.of_phases single (calm.firstUnknown _) (by rw [context]; exact found)
    calm.subqueries_plain sourceCertain window
    (by rw [context]; exact noOverflow) (by rw [context]; exact Resolved.Query.mustFail_of_faultless _ bound _ faultless)
    (by rw [context]; exact Resolved.Query.mayFail_of_faultless _ bound _ plain faultless)
    (by rw [context]; exact distinct)

/-- For every connection, values and calm statement of a query that is no compound, has no
window parameter and has no subqueries: when its source rows {lit}`source` in the context of the
values ({name}`Resolved.EvalContext.bound`) do not possibly fail, it has no failing aggregate over
them ({name}`Resolved.Query.fails`), and its {lit}`DISTINCT` is certain over them
({name}`Resolved.Query.distinctCertain`), the statement is ready at the clock value 0 with the
query itself as the bound query ({name}`Connection.SelectReady`). Proof sketch:
{name}`Connection.SelectReady.of_faultless`; calm expressions have no fault in the context of the
values ({name}`Resolved.Statement.Calm.faultless_nil`). -/
theorem Connection.SelectReady.of_calm (connection : Connection) (parameters : List Value) {query : Resolved.Query}
    {source : Resolved.SourceRows} (calm : (Resolved.Statement.query query []).Calm)
    (single : query.compound = none) (limitParameter : query.limitParameter = none)
    (offsetParameter : query.offsetParameter = none)
    (found : query.source (Resolved.EvalContext.bound parameters) connection.state.database = some source)
    (sourceCertain : source.fault ≠ .may)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) source.rows = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) source.rows = true) :
    connection.SelectReady 0 parameters query [] source query := by
  have faultless := calm.faultless_nil connection parameters (rows := source.rows)
  rw [Connection.queryContext_calm connection parameters query [] calm] at faultless
  exact Connection.SelectReady.of_faultless connection parameters calm single
    (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter) found sourceCertain faultless
    noOverflow distinct

/-- Calm unordered output rule: for every clock, index, connection, values and calm statement of a
query without subqueries that is no compound and has no window parameter, no {lit}`ORDER BY`, no
{lit}`OFFSET` and no {lit}`LIMIT`: when its source rows {lit}`source` in the context of the values
({name}`Resolved.EvalContext.bound`) do not possibly fail, it has no failing aggregate over them
({name}`Resolved.Query.fails`), and its {lit}`DISTINCT` is certain over them
({name}`Resolved.Query.distinctCertain`), the output of its step is the result rows of the query
over the source rows in normal form, whatever the clock. Proof sketch:
{name}`Connection.SelectReady.of_calm` and {name}`resolvedStepOutput_select_unordered`; a calm
statement runs at the clock value 0, in the context of the values
({name}`Connection.queryContext_of_quiet`). -/
theorem resolvedStepOutput_calm_unordered (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {source : Resolved.SourceRows}
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (unordered : query.orderBy = []) (noOffset : query.offset = 0) (noLimit : query.limit = none)
    (found : query.source (Resolved.EvalContext.bound parameters) connection.state.database = some source)
    (sourceCertain : source.fault ≠ .may)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) source.rows = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) source.rows = true) :
    resolvedStepOutput clock index connection parameters (.query query []) =
      .rows (Resolved.normalForm (query.results (Resolved.EvalContext.bound parameters) source.rows)) := by
  have ready := Connection.SelectReady.of_calm connection parameters calm single limitParameter offsetParameter
    found sourceCertain noOverflow distinct
  rw [resolvedStepOutput_select_unordered clock index connection parameters
    (by simp [statementClock, calm.readsClock]) ready unordered noOffset noLimit]
  have context := Connection.queryContext_of_quiet connection parameters query calm.quiet
  exact congrArg (fun context => Output.rows (Resolved.normalForm (query.results context source.rows))) context

/-- Error-free rule: for every connection, values and query statement that is calm
({name}`Resolved.Statement.Calm`), whose query is no compound and has no window parameter, whose
source {lit}`source` is found, whose expressions have no fault over the empty row and over each source
row in the context of the statement, whose aggregates do not overflow over the source rows
({name}`Resolved.Query.fails`) and whose {lit}`DISTINCT` is certain over them
({name}`Resolved.Query.distinctCertain`), the output of its step is no error. The source rows may
have a fault: the output is then no error, and it may be unmodeled. A query without aggregate and
without {lit}`DISTINCT` meets the last two premises by {lit}`rfl`. Proof sketch:
{name}`resolvedStepOutput_query_isError` with the run of {name}`Resolved.Query.run_of_faultless`, which
has no fault, no overflow and no mismatch. -/
theorem resolvedStepOutput_not_isError_of_faultless (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {subqueries : List Resolved.Query}
    {source : Resolved.SourceRows} (calm : (Resolved.Statement.query query subqueries).Calm)
    (single : query.compound = none) (limitParameter : query.limitParameter = none)
    (offsetParameter : query.offsetParameter = none)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none)
    (noOverflow : query.fails (connection.queryContext parameters query subqueries) source.rows = false)
    (distinct : query.distinctCertain (connection.queryContext parameters query subqueries) source.rows = true) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).isError = false := by
  have isError := resolvedStepOutput_query_isError index connection parameters query subqueries source
    calm.readsClock (calm.firstUnknown _) found
  rw [Resolved.Query.run_of_faultless _ single limitParameter offsetParameter calm.query_plain faultless
    noOverflow distinct] at isError
  simpa using isError

end Belay.Sqlite.Model
