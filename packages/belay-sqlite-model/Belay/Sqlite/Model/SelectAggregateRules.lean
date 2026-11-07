import Belay.Sqlite.Model.SelectGroupRules
import Belay.Sqlite.Model.QueryResults

set_option doc.verso true

/-! The rules of the {lit}`aggregate` and {lit}`having` phases of a query (ADR 0027, D1): the
records of an aggregate query ({name}`Belay.Sqlite.Model.Resolved.records`) are the records of its
groups ({lit}`Query.groupRecord`) that {lit}`HAVING` keeps ({lit}`Query.keepsGroup`), in the order of the groups. So an aggregate
query without {lit}`GROUP BY` and {lit}`HAVING` has exactly one record, also over no row, and a
grouped query over no row has none. {lit}`HAVING` reads the row of the group
({name}`Belay.Sqlite.Model.Resolved.Query.groupRow`), which is the model's row: where SQLite's plan
decides the row of a group, native SQLite can read another row. -/

namespace Belay.Sqlite.Model.Resolved

/-- The record of one group of an aggregate query: its result row and its sort values. A scalar
result column reads the row of the group ({name}`Query.groupRow`), or the group's first row when
the column is in {lit}`Query.firstRowColumns`, in the context of the group's aggregate values
({name}`Query.groupContext`); an aggregate column is the aggregate over the group. A sort key of an
expression reads the row of the group, and a sort key that names a result column reads that column
of the result row. {name}`records` gives this record for each group that {lit}`HAVING` keeps. -/
def Query.groupRecord (context : EvalContext) (query : Query) (group : List (List Value)) : Record :=
  let output := query.columns.zipIdx.map fun
    | (.scalar expression, index) => expression.eval (query.groupContext context group)
      (if query.firstRowColumns.contains index then group.headD [] else query.groupRow context group)
    | (.aggregate aggregate, _) => aggregate.eval context group
  (output, query.orderBy.map fun term => match term.key with
    | .expression expression => expression.eval (query.groupContext context group) (query.groupRow context group)
    | .output index => output.getD index .null)

/-- Whether {lit}`HAVING` keeps a group of an aggregate query: each of its conditions is true
({name}`truthy`) over the row of the group ({name}`Query.groupRow`) in the context of the group's
aggregate values ({name}`Query.groupContext`). A condition that is NULL or false does not keep the
group. A query without {lit}`HAVING` keeps every group. -/
def Query.keepsGroup (context : EvalContext) (query : Query) (group : List (List Value)) : Bool :=
  query.having.all fun condition => truthy (condition.eval (query.groupContext context group) (query.groupRow context group))

/-- For every test, function and list: keeping the items that pass the test and mapping each kept
item is the same as mapping each item to an optional value that is present when the item passes. Proof sketch: induction on the
items, by cases on the test. -/
theorem filterMap_ite_eq_map_filter {α β : Type} (keep : α → Bool) (make : α → β) (items : List α) :
    items.filterMap (fun item => if keep item = true then some (make item) else none) =
      (items.filter keep).map make := by
  induction items with
  | nil => rfl
  | cons item rest ih => by_cases kept : keep item = true <;> simp [kept, ih]

/-- Aggregate records rule: for every context, aggregate query and rows, the records of the query
are the records of its groups ({name}`queryGroups`) that {lit}`HAVING` keeps
({name}`Query.keepsGroup`), each made by {name}`Query.groupRecord`, in the order of the groups.
Proof sketch: the aggregate branch of {name}`records` is a filter-map over the groups, which is a
filter followed by a map; induction on the groups. -/
theorem records_aggregate (context : EvalContext) {query : Query} (aggregate : query.aggregate = true)
    (rows : List (List Value)) :
    records context query rows =
      ((queryGroups context query rows).filter (query.keepsGroup context)).map (query.groupRecord context) := by
  unfold records
  simp only [aggregate, ite_true]
  exact filterMap_ite_eq_map_filter (query.keepsGroup context) (query.groupRecord context) _

/-- HAVING rule: for every context, aggregate query, rows and record, the record is a record of the
query exactly when some group of the query keeps it: a group of {name}`queryGroups` that
{lit}`HAVING` keeps ({name}`Query.keepsGroup`) and whose record ({name}`Query.groupRecord`) is the
record. Proof sketch: {name}`records_aggregate` and the members of a filter and a map. -/
theorem mem_records_aggregate (context : EvalContext) {query : Query} (aggregate : query.aggregate = true)
    (rows : List (List Value)) (record : Record) :
    record ∈ records context query rows ↔
      ∃ group ∈ queryGroups context query rows, query.keepsGroup context group = true ∧
        query.groupRecord context group = record := by
  rw [records_aggregate context aggregate]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨group, ⟨member, keeps⟩, rfl⟩
    exact ⟨group, member, keeps, rfl⟩
  · rintro ⟨group, member, keeps, rfl⟩
    exact ⟨group, ⟨member, keeps⟩, rfl⟩

/-- Group-count rule: for every context, aggregate query and rows, the query has at most one record
for each of its groups ({name}`queryGroups`), and exactly one when it has no {lit}`HAVING`. Proof
sketch: {name}`records_aggregate`; a filter is at most as long as its list, and a filter of a test
that is always true is the list. -/
theorem records_aggregate_length (context : EvalContext) {query : Query} (aggregate : query.aggregate = true)
    (rows : List (List Value)) :
    (records context query rows).length ≤ (queryGroups context query rows).length ∧
      (query.having = none → (records context query rows).length = (queryGroups context query rows).length) := by
  rw [records_aggregate context aggregate, List.length_map]
  refine ⟨List.length_filter_le _ _, fun noHaving => ?_⟩
  rw [List.filter_eq_self.mpr (by simp [Query.keepsGroup, noHaving])]

/-- One-row rule: for every context, aggregate query without {lit}`GROUP BY` and without
{lit}`HAVING`, and rows, the query has exactly one record: the record of all the rows as one group
({name}`Query.groupRecord`). This holds also when there is no row: {lit}`SELECT count(*) FROM t`
over an empty table has one record, with the count 0. Proof sketch: {name}`records_aggregate` with
the one group of {name}`queryGroups_ungrouped`, which {lit}`HAVING` keeps. -/
theorem records_ungrouped (context : EvalContext) {query : Query} (aggregate : query.aggregate = true)
    (ungrouped : query.groupBy = []) (noHaving : query.having = none) (rows : List (List Value)) :
    records context query rows = [query.groupRecord context rows] := by
  rw [records_aggregate context aggregate, queryGroups_ungrouped context ungrouped]
  simp [Query.keepsGroup, noHaving]

/-- Empty-group rule: for every context and aggregate query with {lit}`GROUP BY` terms, the query
has no record over no row: there is no group. Proof sketch: {name}`records_aggregate` with no group
({name}`groups_nil`). -/
theorem records_grouped_nil (context : EvalContext) {query : Query} (aggregate : query.aggregate = true)
    (grouped : query.groupBy ≠ []) : records context query [] = [] := by
  rw [records_aggregate context aggregate, queryGroups_grouped context grouped, groups_nil]
  rfl

/-- Result-column rule: for every context, query, group and position of an aggregate result column
{lit}`aggregate`, the result row of the group's record has at that position the aggregate over the
group. Proof sketch: the result row is a map over the numbered columns. -/
theorem Query.groupRecord_aggregate (context : EvalContext) (query : Query) (group : List (List Value))
    {index : Nat} {aggregate : Aggregate} (column : query.columns[index]? = some (.aggregate aggregate)) :
    (query.groupRecord context group).1[index]? = some (aggregate.eval context group) := by
  simp [Query.groupRecord, List.getElem?_map, List.getElem?_zipIdx, column]

/-- Result-column rule, scalar form: for every context, query, group and position of a scalar
result column {lit}`expression` that is not in {lit}`Query.firstRowColumns`, the result row of the
group's record has at that position the expression over the row of the group
({name}`Query.groupRow`) in the context of the group ({name}`Query.groupContext`). Proof sketch:
the result row is a map over the numbered columns. -/
theorem Query.groupRecord_scalar (context : EvalContext) (query : Query) (group : List (List Value))
    {index : Nat} {expression : Expr} (column : query.columns[index]? = some (.scalar expression))
    (notFirst : query.firstRowColumns.contains index = false) :
    (query.groupRecord context group).1[index]? =
      some (expression.eval (query.groupContext context group) (query.groupRow context group)) := by
  have absent : index ∉ query.firstRowColumns := by simpa using notFirst
  simp [Query.groupRecord, List.getElem?_map, List.getElem?_zipIdx, column, absent]

end Belay.Sqlite.Model.Resolved
