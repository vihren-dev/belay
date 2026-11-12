import Belay.Sqlite.Model.Queries.Evaluation.SelectCompoundRules
import Belay.Sqlite.Model.Queries.Evaluation.SelectCalmRule
import Belay.Sqlite.Model.Queries.Evaluation.SelectWindowRules

set_option doc.verso true

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

end Belay.Sqlite.Model
