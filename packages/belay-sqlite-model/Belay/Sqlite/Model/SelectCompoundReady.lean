import Belay.Sqlite.Model.SelectCompoundRules
import Belay.Sqlite.Model.SelectCalmRule
import Belay.Sqlite.Model.SelectWindowRules

set_option doc.verso true

/-! The readiness of a compound query statement (ADR 0027, D5, phase {lit}`compound`): a calm
statement of a compound query whose window binds is ready ({lit}`Connection.SelectReady`) when
each term ends without a failure for the outer row and each operator keeps certain rows. Its
results are then the rows of the compound ({lit}`Compound.rows`) in an order that the
{lit}`ORDER BY` permits. -/

namespace Belay.Sqlite.Model

namespace Resolved

/-- For every context, query that is the compound {lit}`compound` and rows, the rows of the
query's records ({name}`Query.uniqueRecords`) are the rows of the compound for the first row
({name}`Compound.rows`), in order. Proof sketch: {name}`Query.compoundRecords` pairs each row of the
compound with its sort keys. -/
theorem Query.uniqueRecords_compound (context : EvalContext) {query : Query} {compound : Compound}
    (shape : query.compound = some compound) (rows : List (List Value)) :
    (query.uniqueRecords context rows).map Prod.fst = compound.rows context (rows.headD []) := by
  simp [Query.uniqueRecords, shape, Query.compoundRecords, Function.comp_def]

/-- Compound result rule: for every context, query that is the compound {lit}`compound` with
{lit}`OFFSET` 0 and no {lit}`LIMIT`, rows and result that the model permits
({name}`Query.possibleResults`), the result is a permutation of the rows of the compound for the
first row ({name}`Compound.rows`). Proof sketch: {name}`Query.perm_of_mem_possibleResults` and
{name}`Query.uniqueRecords_compound`. -/
theorem Query.perm_of_mem_possibleResults_compound {context : EvalContext} {query : Query} {compound : Compound}
    (shape : query.compound = some compound) (offset : query.offset = 0) (limit : query.limit = none)
    {rows result : List (List Value)} (member : result ∈ query.possibleResults context rows) :
    result.Perm (compound.rows context (rows.headD [])) :=
  Query.uniqueRecords_compound context shape rows ▸ Query.perm_of_mem_possibleResults offset limit member

end Resolved

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
