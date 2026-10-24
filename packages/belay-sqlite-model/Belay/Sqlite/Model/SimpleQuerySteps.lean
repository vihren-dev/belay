import Belay.Sqlite.Model.SimpleQueryLaws
import Belay.Sqlite.Model.QueryStatementOutput
import Belay.Sqlite.Model.StatementCalm

set_option doc.verso true

/-! The output of a simple query statement (ADR 0017, S4): a statement whose query is simple
({name}`Belay.Sqlite.Model.Resolved.Query.Simple`), has no subquery and is calm
({name}`Belay.Sqlite.Model.Resolved.Statement.Calm`), has rows exactly when {lit}`WHERE` is true for a row of its source, has no
rows exactly when it is not true for any row, and is never an error. -/

namespace Belay.Sqlite.Model

/-- The context in which a calm statement without subqueries evaluates its expressions: the clock
value 0, no counter, and the values bound to its parameters. -/
abbrev Resolved.EvalContext.bound (parameters : List Value) : Resolved.EvalContext :=
  { Resolved.EvalContext.plain 0 with parameters }

/-- For every connection, values and calm statement of a query without subqueries, the context of
the query on the connection is the context of the values ({name}`Resolved.EvalContext.bound`): the
statement reads no counter, so the context knows none. Proof sketch: the statement reads no counters
({name}`Resolved.Statement.Calm.counterReads`), and the view of the counters for no read is no counter. -/
theorem Connection.queryContext_of_calm (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (calm : (Resolved.Statement.query query []).Calm) :
    connection.queryContext parameters query [] = Resolved.EvalContext.bound parameters := by
  simp only [Connection.queryContext, calm.counterReads, Resolved.statementContext_nil]
  rfl

/-- For every simple query statement without subqueries, whose expressions have no fallible call,
the faults of its run are none: the context of the statement is quiet, so the run is the one result
({name}`Resolved.Query.Simple.run_plain`). The run is over any rows. -/
theorem Connection.run_simple (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (simple : query.Simple) (plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true)
    (rows : List (List Value)) :
    query.run (connection.queryContext parameters query []) rows =
      { rows := query.results (connection.queryContext parameters query []) rows, fault := .none, overflow := false,
        mismatch := false } :=
  simple.run_plain _ (fun _ _ => ⟨rfl, rfl, rfl⟩) plain rows

/-- For every simple query statement without subqueries, whose expressions have no fallible call,
that is calm ({name}`Resolved.Statement.Calm`), and whose source rows {lit}`source` have no fault, the
output of its step has rows exactly when {lit}`WHERE` is true for some row of the source. Proof
sketch: {name}`resolvedStepOutput_query_hasRows`; the window binds to the query itself, the run has
no fault ({name}`Connection.run_simple`), and {name}`Resolved.Query.Simple.results_ne_nil_iff` turns
the one result into the rows that {lit}`WHERE` keeps. -/
theorem resolvedStepOutput_simple_hasRows (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : query.source (connection.queryContext parameters query []) connection.state.database = some source)
    (clean : source.fault = .none) :
    (resolvedStepOutput none index connection parameters (.query query [])).hasRows = true ↔
      ∃ row ∈ source.rows, query.filter.all
        (fun condition => Resolved.truthy (condition.eval (connection.queryContext parameters query []) row)) = true := by
  rw [resolvedStepOutput_query_hasRows index connection parameters query query [] source calm.readsClock
    (calm.firstUnknown _) found (simple.bindWindow parameters),
    Connection.run_simple connection parameters query simple calm.query_plain]
  simp [Resolved.Query.nestedSubqueries, simple.compound, Resolved.subqueriesPlain, clean,
    simple.results_ne_nil_iff]

/-- For every simple query statement as in {name}`resolvedStepOutput_simple_hasRows`, the output of
its step has no rows exactly when {lit}`WHERE` is not true for any row of the source. Proof sketch:
as for {name}`resolvedStepOutput_simple_hasRows`, with
{name}`Resolved.Query.Simple.results_eq_nil_iff`. -/
theorem resolvedStepOutput_simple_hasNoRows (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : query.source (connection.queryContext parameters query []) connection.state.database = some source)
    (clean : source.fault = .none) :
    (resolvedStepOutput none index connection parameters (.query query [])).hasNoRows = true ↔
      ∀ row ∈ source.rows, query.filter.all
        (fun condition => Resolved.truthy (condition.eval (connection.queryContext parameters query []) row)) = false := by
  rw [resolvedStepOutput_query_hasNoRows index connection parameters query query [] source calm.readsClock
    (calm.firstUnknown _) found (simple.bindWindow parameters),
    Connection.run_simple connection parameters query simple calm.query_plain]
  simp [Resolved.Query.nestedSubqueries, simple.compound, Resolved.subqueriesPlain, clean,
    simple.results_eq_nil_iff]

/-- For every simple query statement as in {name}`resolvedStepOutput_simple_hasRows`, the output of
its step is no error: the run has no window mismatch, no overflow and no fault. Proof sketch:
{name}`resolvedStepOutput_query_isError` and {name}`Connection.run_simple`. -/
theorem resolvedStepOutput_simple_not_isError (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : query.source (connection.queryContext parameters query []) connection.state.database = some source) :
    (resolvedStepOutput none index connection parameters (.query query [])).isError = false := by
  have := resolvedStepOutput_query_isError index connection parameters query [] source calm.readsClock
    (calm.firstUnknown _) found
  rw [Connection.run_simple connection parameters query simple calm.query_plain] at this
  simpa using this

end Belay.Sqlite.Model
