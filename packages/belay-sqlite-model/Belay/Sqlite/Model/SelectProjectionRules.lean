import Belay.Sqlite.Model.SelectWindowRules

set_option doc.verso true

/-! The rules of the filter and projection phases of a SELECT (ADR 0027 D1): {lit}`WHERE` keeps a
sublist of the source rows, and a query without aggregation, {lit}`DISTINCT` or a compound gives
one result row for each row that {lit}`WHERE` keeps ({lit}`Query.rowOutput`).
With the result rules ({lit}`SelectWindowRules.lean`), every result that the model permits for such a
query is a permutation of the result rows of a sublist of the kept rows, and of all of them without
a window. -/

namespace Belay.Sqlite.Model.Resolved

/-- The result row of a query without aggregation for one source row: each scalar column's value
on the row, and each aggregate column over the list of that one row, as {name}`records` gives
them. -/
def Query.rowOutput (context : EvalContext) (query : Query) (row : List Value) : List Value :=
  query.columns.map fun
    | .scalar expression => expression.eval context row
    | .aggregate aggregate => aggregate.eval context [row]

/-- Filter rule: for every context, query and rows, the rows that {lit}`WHERE` keeps
({name}`filtered`) are a sublist of the rows. -/
theorem filtered_sublist (context : EvalContext) (query : Query) (rows : List (List Value)) :
    (filtered context query rows).Sublist rows := List.filter_sublist

/-- Filter rule: for every context, query without {lit}`WHERE` and rows, {lit}`WHERE` keeps all
the rows ({name}`filtered`). -/
theorem filtered_of_filter_none (context : EvalContext) {query : Query} (noFilter : query.filter = none)
    (rows : List (List Value)) : filtered context query rows = rows := by
  simp [filtered, noFilter]

/-- Projection rule: for every context, query without aggregation and rows, the rows of the
query's records ({name}`records`) are the result rows of the rows, in order
({name}`Query.rowOutput`). Proof sketch: without aggregation, {name}`records` maps each row to
its result row and its sort values. -/
theorem records_outputs_plain (context : EvalContext) {query : Query} (plain : query.aggregate = false)
    (rows : List (List Value)) :
    (records context query rows).map Prod.fst = rows.map (query.rowOutput context) := by
  simp [records, plain, Query.rowOutput, Function.comp_def]
  intro _ _ _ _
  rfl

/-- Projection rule: for every context, query that is no compound and has no {lit}`DISTINCT` and
no aggregation, and rows, the rows of the query's records ({name}`Query.uniqueRecords`) are the
result rows ({name}`Query.rowOutput`) of the rows that {lit}`WHERE` keeps ({name}`filtered`), in
order. Proof sketch: without a compound or {lit}`DISTINCT`, the records are {name}`records` of the
kept rows ({name}`records_outputs_plain`). -/
theorem Query.uniqueRecords_outputs_plain (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (plain : query.aggregate = false) (rows : List (List Value)) :
    (query.uniqueRecords context rows).map Prod.fst = (filtered context query rows).map (query.rowOutput context) := by
  simp only [Query.uniqueRecords, single, noDistinct]
  exact records_outputs_plain context plain _

/-- Plain result rule: for every context, query that is no compound and has no {lit}`DISTINCT` and
no aggregation, rows and result that the model permits ({name}`Query.possibleResults`), some sublist
of the rows that {lit}`WHERE` keeps ({name}`filtered`) has result rows ({name}`Query.rowOutput`) of
which the result is a permutation. This holds for every {lit}`ORDER BY`, {lit}`OFFSET` and
{lit}`LIMIT`. Proof sketch: {name}`Query.exists_sublist_of_mem_possibleResults` with
{name}`Query.uniqueRecords_outputs_plain`; a sublist of the mapped rows is the map of a sublist. -/
theorem Query.exists_rows_of_mem_possibleResults_plain {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (single : query.compound = none) (noDistinct : query.distinct = none)
    (plain : query.aggregate = false) (member : result ∈ query.possibleResults context rows) :
    ∃ picked : List (List Value), picked.Sublist (filtered context query rows) ∧ result.Perm (picked.map (query.rowOutput context)) := by
  obtain ⟨outputs, sublist, perm⟩ := Query.exists_sublist_of_mem_possibleResults member
  rw [Query.uniqueRecords_outputs_plain context single noDistinct plain] at sublist
  obtain ⟨picked, pickedSublist, rfl⟩ := List.sublist_map_iff.mp sublist
  exact ⟨picked, pickedSublist, perm⟩

/-- Plain row rule: for every context, query that is no compound and has no {lit}`DISTINCT` and no
aggregation, rows, result that the model permits and row of the result, some source row is in the
rows, the {lit}`WHERE` condition, if any, is true for it, and the row is its result row
({name}`Query.rowOutput`). Proof sketch: the row is the row of a record
({name}`Query.mem_of_mem_possibleResults`), which is the result row of a kept row
({name}`Query.uniqueRecords_outputs_plain`, {name}`mem_filtered`). -/
theorem Query.mem_possibleResults_plain {context : EvalContext} {query : Query} {rows result : List (List Value)}
    (single : query.compound = none) (noDistinct : query.distinct = none) (plain : query.aggregate = false)
    (member : result ∈ query.possibleResults context rows) {row : List Value} (inResult : row ∈ result) :
    ∃ source ∈ rows, query.filter.all (fun condition => truthy (condition.eval context source)) = true ∧
      row = query.rowOutput context source := by
  have found := Query.mem_of_mem_possibleResults member inResult
  rw [Query.uniqueRecords_outputs_plain context single noDistinct plain] at found
  obtain ⟨source, kept, rfl⟩ := List.mem_map.mp found
  exact ⟨source, ((mem_filtered context query rows source).mp kept).1,
    ((mem_filtered context query rows source).mp kept).2, rfl⟩

/-- Plain cardinality rule: for every context, query that is no compound and has no
{lit}`DISTINCT`, aggregation, {lit}`OFFSET` or {lit}`LIMIT`, rows and result that the model permits,
the result is a permutation of the result rows ({name}`Query.rowOutput`) of all the rows that
{lit}`WHERE` keeps ({name}`filtered`): it has as many rows, and each row as often. Proof sketch:
{name}`Query.perm_of_mem_possibleResults` with {name}`Query.uniqueRecords_outputs_plain`. -/
theorem Query.perm_of_mem_possibleResults_plain {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (single : query.compound = none) (noDistinct : query.distinct = none)
    (plain : query.aggregate = false) (offset : query.offset = 0) (limit : query.limit = none)
    (member : result ∈ query.possibleResults context rows) :
    result.Perm ((filtered context query rows).map (query.rowOutput context)) :=
  Query.uniqueRecords_outputs_plain context single noDistinct plain rows ▸
    Query.perm_of_mem_possibleResults offset limit member

end Belay.Sqlite.Model.Resolved
