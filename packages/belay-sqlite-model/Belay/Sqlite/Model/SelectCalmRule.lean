import Belay.Sqlite.Model.SelectRunRule
import Belay.Sqlite.Model.StatementCalm
import Belay.Sqlite.Model.QueryPlainLaws

set_option doc.verso true

/-! The readiness of a calm query statement (ADR 0027, D5): a statement whose expressions have no
fallible call and read no clock and no counter ({lit}`Resolved.Statement.Calm`) evaluates in the
context of its values alone, its expressions have no fault, and it is ready
({lit}`Connection.SelectReady`) when its source does not possibly fail, it does not overflow, and
its {lit}`DISTINCT` is certain. -/

namespace Belay.Sqlite.Model

/-- The context in which a calm statement without subqueries evaluates its expressions: the clock
value 0, no counter, and the values bound to its parameters. -/
abbrev Resolved.EvalContext.bound (parameters : List Value) : Resolved.EvalContext :=
  { Resolved.EvalContext.plain 0 with parameters }

/-- For every list of values, the values bound to the parameters of the context of the values are the values. Proof
sketch: the definition computes. -/
theorem Resolved.EvalContext.bound_parameters (parameters : List Value) :
    (Resolved.EvalContext.bound parameters).parameters = parameters := rfl

/-- For every connection, values and calm statement of a query without subqueries, the context of
the query on the connection is the context of the values ({name}`Resolved.EvalContext.bound`): the
statement reads no counter, so the context knows none. Proof sketch: the statement reads no counters
({name}`Resolved.Statement.Calm.counterReads`), and the view of the counters for no read is no counter. -/
theorem Connection.queryContext_of_calm (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (calm : (Resolved.Statement.query query []).Calm) :
    connection.queryContext parameters query [] = Resolved.EvalContext.bound parameters := by
  simp only [Connection.queryContext, calm.counterReads, Resolved.statementContext_nil]
  rfl

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
  rw [Connection.queryContext_of_calm connection parameters query calm]
  exact Resolved.Expr.fault_of_plain _ (fun _ _ => ⟨rfl, rfl, rfl⟩) row expression (plain expression member)

/-- For every connection, values and calm statement of a query that is no compound, has no
window parameter and has no subqueries: when its source rows {lit}`source` in the context of the
values ({name}`Resolved.EvalContext.bound`) do not possibly fail, it has no failing aggregate over
them ({name}`Resolved.Query.fails`), and its {lit}`DISTINCT` is certain over them
({name}`Resolved.Query.distinctCertain`), the statement is ready at the clock value 0 with the
query itself as the bound query ({name}`Connection.SelectReady`). Proof sketch:
{name}`Connection.SelectReady.of_phases`; the context is that of the values
({name}`Connection.queryContext_of_calm`), and calm expressions have no fault
({name}`Resolved.Statement.Calm.faultless_nil`). -/
theorem Connection.SelectReady.of_calm (connection : Connection) (parameters : List Value) {query : Resolved.Query}
    {source : Resolved.SourceRows} (calm : (Resolved.Statement.query query []).Calm)
    (single : query.compound = none) (limitParameter : query.limitParameter = none)
    (offsetParameter : query.offsetParameter = none)
    (found : query.source (Resolved.EvalContext.bound parameters) connection.state.database = some source)
    (sourceCertain : source.fault ≠ .may)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) source.rows = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) source.rows = true) :
    connection.SelectReady 0 parameters query [] source query := by
  have context : connection.queryContextAt 0 parameters query [] = Resolved.EvalContext.bound parameters :=
    Connection.queryContext_of_calm connection parameters query calm
  have faultless := calm.faultless_nil connection parameters (rows := source.rows)
  refine Connection.SelectReady.of_phases single (calm.firstUnknown _) (by rw [context]; exact found)
    calm.subqueries_plain sourceCertain
    (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter)
    (by rw [context]; exact noOverflow) (Resolved.Query.mustFail_of_faultless _ query source.rows faultless)
    (Resolved.Query.mayFail_of_faultless _ query source.rows calm.query_plain faultless)
    (by rw [context]; exact distinct)

end Belay.Sqlite.Model
