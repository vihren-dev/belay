import Belay.Sqlite.Model.Queries.Evaluation.SelectCompoundRules
import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule

set_option doc.verso true

/-! The readiness of a compound query statement (ADR 0027, D5, phase {lit}`compound`): a calm
statement of a compound query whose window binds is ready ({lit}`Connection.SelectReady`) when
each term ends without a failure for the outer row and each operator keeps certain rows. Its
results are then the rows of the compound ({lit}`Compound.rows`) in an order that the
{lit}`ORDER BY` permits. -/

namespace Belay.Sqlite.Model

/-- Compound readiness rule: for every connection, values and calm statement
({name}`Resolved.Statement.Calm`) of the compound {lit}`compound` with subqueries, source rows
{lit}`source` in the context of the statement ({name}`Resolved.EvalContext.statement`) and window
that binds to the query {lit}`bound`, the statement is ready at the clock value 0
({name}`Connection.SelectReady`) when:
- the source does not possibly fail;
- the run of each term of the compound ({name}`Resolved.Compound.terms`) for the first source row
  ends with {lean}`Resolved.RunEnd.done`;
- each operator keeps certain rows ({name}`Resolved.Compound.combined`).

Proof sketch: the compound ends done ({name}`Resolved.Compound.ending_done`), so its run has no
mismatch, no overflow and no fault. -/
theorem Connection.SelectReady.of_compound (connection : Connection) (parameters : List Value)
    {query bound : Resolved.Query} {subqueries : List Resolved.Query} {source : Resolved.SourceRows}
    {compound : Resolved.Compound}
    (calm : (Resolved.Statement.query query subqueries).Calm) (shape : query.compound = some compound)
    (found : query.source (Resolved.EvalContext.statement parameters connection.state.database subqueries)
      connection.state.database = some source)
    (sourceCertain : source.fault ≠ .may) (window : query.bindWindow parameters = some bound)
    (done : ∀ index ∈ compound.terms,
      ((Resolved.EvalContext.statement parameters connection.state.database subqueries).subqueries index
        (source.rows.headD [])).ending = .done)
    (certain : (compound.combined (Resolved.EvalContext.statement parameters connection.state.database subqueries)
      (source.rows.headD [])).2 = true) :
    connection.SelectReady 0 parameters query subqueries source bound := by
  have context : connection.queryContextAt 0 parameters query subqueries =
      Resolved.EvalContext.statement parameters connection.state.database subqueries :=
    Connection.queryContext_calm connection parameters query subqueries calm
  have ended := Resolved.Compound.ending_done
    (Resolved.EvalContext.statement parameters connection.state.database subqueries) compound
    (source.rows.headD []) (query := query) (by simpa [Resolved.statementContext_parameters] using window) done
  simp only [List.headD_eq_head?_getD] at ended certain
  refine ⟨calm.firstUnknown _, by rw [context]; exact found, calm.subqueries_plain, sourceCertain, window, ?_, ?_, ?_⟩ <;>
    simp [context, Resolved.Query.run, shape, Resolved.Query.compoundRun, ended, certain]

end Belay.Sqlite.Model
