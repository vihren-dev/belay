import Belay.Sqlite.Model.SimpleQueryLaws
import Belay.Sqlite.Model.QueryStatementOutput
import Belay.Sqlite.Model.SelectCalmRule

set_option doc.verso true

/-! The output of a simple query statement (ADR 0017, S4): a statement whose query is simple
({name}`Belay.Sqlite.Model.Resolved.Query.Simple`), under the context hypotheses of each theorem,
has rows exactly when {lit}`WHERE` is true for a source row, has no rows exactly when it is true
for none, and is never an error. All variants require
{name}`Belay.Sqlite.Model.Resolved.Statement.Calm`. Faultless variants allow subqueries. Their
has-rows and has-no-rows equivalences require a fault-free source; their no-error law permits
source faults. Plain variants require no subqueries. -/

namespace Belay.Sqlite.Model

/-- For every simple query statement whose expressions have no fallible call, that is calm
({name}`Resolved.Statement.Calm`), and whose source rows {lit}`source` have no fault, with expressions
that have no fault over the empty row and over each source row in the context of the statement, the
output of its step has rows exactly when {lit}`WHERE` is true for some row of the source. The
statement may have subqueries. Proof
sketch: {name}`resolvedStepOutput_query_hasRows`; the window binds to the query itself, the run has
no fault ({name}`Resolved.Query.Simple.run_of_faultless`), and {name}`Resolved.Query.Simple.results_ne_nil_iff` turns
the one result into the rows that {lit}`WHERE` keeps. -/
theorem resolvedStepOutput_simple_hasRows_of_faultless (index : Nat) (connection : Connection)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query) (simple : query.Simple)
    (source : Resolved.SourceRows) (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (clean : source.fault = .none)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).hasRows = true ↔
      ∃ row ∈ source.rows, query.filter.all
        (fun condition => Resolved.truthy (condition.eval (connection.queryContext parameters query subqueries) row)) = true := by
  rw [resolvedStepOutput_query_hasRows index connection parameters query query subqueries source calm.readsClock
    (calm.firstUnknown _) found (simple.bindWindow parameters),
    simple.run_of_faultless _ calm.query_plain source.rows faultless]
  simp [calm.subqueries_plain, clean, simple.results_ne_nil_iff]

/-- For every simple query statement as in {name}`resolvedStepOutput_simple_hasRows_of_faultless`, the output of
its step has no rows exactly when {lit}`WHERE` is not true for any row of the source. Proof sketch:
as for {name}`resolvedStepOutput_simple_hasRows_of_faultless`, with
{name}`Resolved.Query.Simple.results_eq_nil_iff`. -/
theorem resolvedStepOutput_simple_hasNoRows_of_faultless (index : Nat) (connection : Connection)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query) (simple : query.Simple)
    (source : Resolved.SourceRows) (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (clean : source.fault = .none)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).hasNoRows = true ↔
      ∀ row ∈ source.rows, query.filter.all
        (fun condition => Resolved.truthy (condition.eval (connection.queryContext parameters query subqueries) row)) = false := by
  rw [resolvedStepOutput_query_hasNoRows index connection parameters query query subqueries source calm.readsClock
    (calm.firstUnknown _) found (simple.bindWindow parameters),
    simple.run_of_faultless _ calm.query_plain source.rows faultless]
  simp [calm.subqueries_plain, clean, simple.results_eq_nil_iff]

/-- For every simple query statement that is calm ({name}`Resolved.Statement.Calm`), whose source is found, and
whose expressions have no fault over the empty row and over each source row in the context of the statement,
the output of its step is no error: the run has no window mismatch, no overflow and no fault. The source
rows may have a fault: the output is then no error, and it may be unmodeled. Proof sketch:
{name}`resolvedStepOutput_query_isError` and {name}`Resolved.Query.Simple.run_of_faultless`. -/
theorem resolvedStepOutput_simple_not_isError_of_faultless (index : Nat) (connection : Connection)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query) (simple : query.Simple)
    (source : Resolved.SourceRows) (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (connection.queryContext parameters query subqueries) row).2 = .none) :
    (resolvedStepOutput none index connection parameters (.query query subqueries)).isError = false := by
  have := resolvedStepOutput_query_isError index connection parameters query subqueries source calm.readsClock
    (calm.firstUnknown _) found
  rw [simple.run_of_faultless _ calm.query_plain source.rows faultless] at this
  simpa using this

/-- For every simple query statement without subqueries, whose expressions have no fallible call,
that is calm, and whose source rows {lit}`source` have no fault, the
output of its step has rows exactly when {lit}`WHERE` is true for some row of the source. Proof
sketch: {name}`resolvedStepOutput_simple_hasRows_of_faultless`; a quiet context gives no fault
({name}`Resolved.Expr.fault_of_plain`). -/
theorem resolvedStepOutput_simple_hasRows (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : query.source (connection.queryContext parameters query []) connection.state.database = some source)
    (clean : source.fault = .none) :
    (resolvedStepOutput none index connection parameters (.query query [])).hasRows = true ↔
      ∃ row ∈ source.rows, query.filter.all
        (fun condition => Resolved.truthy (condition.eval (connection.queryContext parameters query []) row)) = true :=
  resolvedStepOutput_simple_hasRows_of_faultless index connection parameters query [] simple source calm found clean
    (calm.faultless_nil connection parameters)

/-- For every simple query statement as in {name}`resolvedStepOutput_simple_hasRows`, the output of
its step has no rows exactly when {lit}`WHERE` is not true for any row of the source. Proof sketch:
{name}`resolvedStepOutput_simple_hasNoRows_of_faultless`. -/
theorem resolvedStepOutput_simple_hasNoRows (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : query.source (connection.queryContext parameters query []) connection.state.database = some source)
    (clean : source.fault = .none) :
    (resolvedStepOutput none index connection parameters (.query query [])).hasNoRows = true ↔
      ∀ row ∈ source.rows, query.filter.all
        (fun condition => Resolved.truthy (condition.eval (connection.queryContext parameters query []) row)) = false :=
  resolvedStepOutput_simple_hasNoRows_of_faultless index connection parameters query [] simple source calm found clean
    (calm.faultless_nil connection parameters)

/-- For every simple query statement as in {name}`resolvedStepOutput_simple_hasRows`, the output of
its step is no error. Proof sketch: {name}`resolvedStepOutput_simple_not_isError_of_faultless`. -/
theorem resolvedStepOutput_simple_not_isError (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : query.source (connection.queryContext parameters query []) connection.state.database = some source) :
    (resolvedStepOutput none index connection parameters (.query query [])).isError = false :=
  resolvedStepOutput_simple_not_isError_of_faultless index connection parameters query [] simple source calm found
    (calm.faultless_nil connection parameters)

end Belay.Sqlite.Model
