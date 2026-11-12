import Belay.Sqlite.Model.Queries.Evaluation.GroupPartition
import Belay.Sqlite.Model.Queries.Evaluation.GroupRow

set_option doc.verso true

/-! The rules of the {lit}`group` phase of a query (ADR 0027, D1): the groups of an aggregate query
({name}`Belay.Sqlite.Model.Resolved.queryGroups`) are all its rows as one group without
{lit}`GROUP BY`, and otherwise a partition of its rows by the grouping terms: each row is in exactly
one group as often as in the rows, each group has a row, each row of a group has the key of the
group's first row under the terms' collations, and the first rows of two groups have different keys.
Equal keys under a collation do not make equal values: {lit}`'a'` and {lit}`'A'` are one group under
{lit}`NOCASE`. The row from which a group's expressions read is one of its rows. -/

namespace Belay.Sqlite.Model.Resolved

/-- Partition rule: for every context, grouping terms and rows, the groups of the rows
({name}`groups`):
- one after the other, are a permutation of the rows;
- are formed ({name}`GroupsFormed`): each group has a first row, and each later row of the group is
  the same as it ({name}`sameGroup`);
- are apart ({name}`GroupsApart`): the first row of a later group is not the same as the first row
  of an earlier group.

Proof sketch: {name}`groups_eq_fold` and {name}`groupFold_flatten_perm` and
{name}`groupFold_formed_apart` from no groups. -/
theorem groups_partition (context : EvalContext) (terms : List (Expr × Collation)) (rows : List (List Value)) :
    (groups context terms rows).flatten.Perm rows ∧ GroupsFormed (sameGroup context terms) (groups context terms rows) ∧
      GroupsApart (sameGroup context terms) (groups context terms rows) := by
  rw [groups_eq_fold]
  obtain ⟨formed, apart⟩ := groupFold_formed_apart (sameGroup context terms) rows [] (by simp [GroupsFormed])
    (by simp [GroupsApart])
  exact ⟨by simpa using groupFold_flatten_perm (sameGroup context terms) rows [], formed, apart⟩

/-- For every context and grouping terms, the rows of no row have no group. Proof sketch:
{name}`groups` of no row computes to no group. -/
@[simp] theorem groups_nil (context : EvalContext) (terms : List (Expr × Collation)) : groups context terms [] = [] :=
  rfl

/-- Ungrouped rule: for every context, query without {lit}`GROUP BY` terms and rows, the groups of
the query are one group of all the rows, also when there is no row. Proof sketch:
{name}`queryGroups` takes its branch without terms. -/
theorem queryGroups_ungrouped (context : EvalContext) {query : Query} (ungrouped : query.groupBy = [])
    (rows : List (List Value)) : queryGroups context query rows = [rows] := by
  simp [queryGroups, ungrouped]

/-- Grouped rule: for every context, query with {lit}`GROUP BY` terms and rows, the groups of the
query are the groups of the rows by the terms ({name}`groups`). Proof sketch: {name}`queryGroups`
takes its branch with terms. -/
theorem queryGroups_grouped (context : EvalContext) {query : Query} (grouped : query.groupBy ≠ [])
    (rows : List (List Value)) : queryGroups context query rows = groups context query.groupBy rows := by
  simp [queryGroups, List.isEmpty_iff, grouped]

/-- Multiplicity rule: for every context, query, rows and row, the groups of the query
({name}`queryGroups`), one after the other, have the row as often as the rows have it, with or
without {lit}`GROUP BY`. Proof sketch: without terms the groups are the rows; with terms they are a
permutation of them ({name}`groups_partition`). -/
theorem queryGroups_count (context : EvalContext) (query : Query) (rows : List (List Value)) (row : List Value) :
    (queryGroups context query rows).flatten.count row = rows.count row := by
  by_cases grouped : query.groupBy = []
  · simp [queryGroups_ungrouped context grouped]
  · rw [queryGroups_grouped context grouped]
    exact (groups_partition context query.groupBy rows).1.count_eq row

/-- Group-member rule: for every context, query with {lit}`GROUP BY` terms, rows and group of the
query ({name}`queryGroups`), the group has a first row, each later row of the group is the same as
it under the grouping terms ({name}`sameGroup`), and each row of the group is one of the rows. Proof
sketch: {name}`groups_partition`; a member of a group is a member of the flattened groups. -/
theorem mem_queryGroups (context : EvalContext) {query : Query} (grouped : query.groupBy ≠ [])
    {rows group : List (List Value)} (member : group ∈ queryGroups context query rows) :
    (∃ first rest, group = first :: rest ∧ ∀ later ∈ rest, sameGroup context query.groupBy later first = true) ∧
      ∀ row ∈ group, row ∈ rows := by
  rw [queryGroups_grouped context grouped] at member
  obtain ⟨perm, formed, -⟩ := groups_partition context query.groupBy rows
  exact ⟨formed group member, fun row inGroup => perm.subset (List.mem_flatten.mpr ⟨group, member, inGroup⟩)⟩

/-- Group-row rule: for every context, query and group with a row, the row from which the group's
expressions read ({name}`Query.groupRow`) is one of the group's rows: the first row, or for a
{lit}`min` or {lit}`max` call that decides the row, the first row with the call's value, or the
last row when every operand is NULL. Proof sketch: by cases on the deciding call; a found row is a
member, and the first and the last row of a nonempty list are members. -/
theorem Query.groupRow_mem (context : EvalContext) (query : Query) {group : List (List Value)}
    (nonempty : group ≠ []) : query.groupRow context group ∈ group := by
  have first : group.headD [] ∈ group := by
    cases group with
    | nil => exact absurd rfl nonempty
    | cons head tail => exact List.mem_cons_self ..
  unfold Query.groupRow
  split
  · rename_i call _
    unfold Aggregate.decidingRow
    split
    all_goals first
      | exact first
      | (dsimp only
         split
         · cases group with
           | nil => exact absurd rfl nonempty
           | cons head tail =>
             rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (List.cons_ne_nil head tail)]
             exact List.getLast_mem _
         · cases found : group.find? _ with
           | none => exact first
           | some row => exact List.mem_of_find?_eq_some found)
  · exact first

end Belay.Sqlite.Model.Resolved
