import SelectAutomationCore

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027's prototype of the phase rules (deep review, finding 6): one theorem per phase of
{name}`Belay.Sqlite.Model.Resolved.Query.results`, each about what the phase's output keeps from
its input, stated for every query that meets the phase's own premises; none names a query shape. -/

namespace SelectAutomation
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- Projection rule, scalar form: for every context, query that is no aggregate query, rows and
record of {name}`Resolved.records`, some row of the rows gives the record's output: each result
column evaluated over that row. Proof sketch: the scalar branch of {name}`Resolved.records` is a
map over the rows. -/
theorem mem_records_scalar (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (record : Resolved.Record) (scalar : query.aggregate = false) (member : record ∈ Resolved.records context query rows) :
    ∃ row ∈ rows, record.1 = query.columns.map fun
      | .scalar expression => expression.eval context row
      | .aggregate aggregate => aggregate.eval context [row] := by
  unfold Resolved.records at member
  simp only [scalar, Bool.false_eq_true, ite_false, List.mem_map] at member
  obtain ⟨row, h, rfl⟩ := member
  exact ⟨row, h, rfl⟩

/-- Projection rule, grouped form: for every context, aggregate query, rows and record of
{name}`Resolved.records`, some group of {name}`Resolved.queryGroups` passes {lit}`HAVING` over
its row ({name}`Resolved.Query.groupRow`) in its context ({name}`Resolved.Query.groupContext`),
and the record's output is each result column over that group: a scalar column over the row of
the group, or over its first row for a column of {name}`Resolved.Query.firstRowColumns`; an
aggregate column over the group. Proof sketch: the aggregate branch of {name}`Resolved.records`
is a filter-map over the groups. -/
theorem mem_records_aggregate (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (record : Resolved.Record) (aggregate : query.aggregate = true)
    (member : record ∈ Resolved.records context query rows) :
    ∃ group ∈ Resolved.queryGroups context query rows,
      query.having.all (fun condition =>
        Resolved.truthy (condition.eval (query.groupContext context group) (query.groupRow context group))) = true ∧
      record.1 = query.columns.zipIdx.map fun
        | (.scalar expression, index) => expression.eval (query.groupContext context group)
            (if query.firstRowColumns.contains index then group.headD [] else query.groupRow context group)
        | (.aggregate call, _) => call.eval context group := by
  unfold Resolved.records at member
  simp only [aggregate, ite_true, List.mem_filterMap] at member
  obtain ⟨group, h, found⟩ := member
  refine ⟨group, h, ?_⟩
  split at found
  · rename_i having
    cases found
    exact ⟨having, rfl⟩
  · exact absurd found (by simp)

/-- Grouping rule, general form: for every test, property of items and property of groups that
holds of a group of one allowed item and stays when an allowed item joins a group, every group of
the fold of {name}`Resolved.groupStep` over allowed items, from groups with the property, has the
property. Proof sketch: induction on the items; a joining item changes one group
({name}`List.mem_or_eq_of_mem_set`) and a new group is one item. -/
theorem groupFold_property {α : Type} (same : α → α → Bool) (allowed : α → Prop) (good : List α → Prop)
    (single : ∀ item, allowed item → good [item])
    (join : ∀ group item, good group → allowed item → good (group ++ [item])) :
    ∀ (items : List α) (found : List (List α)), (∀ item ∈ items, allowed item) → (∀ group ∈ found, good group) →
      ∀ group ∈ items.foldl (Resolved.groupStep same) found, good group
  | [], _, _, start, group, member => start group member
  | item :: rest, found, items, start, group, member => by
    simp only [List.foldl_cons] at member
    refine groupFold_property same allowed good single join rest _ (fun x h => items x (List.mem_cons_of_mem _ h)) ?_
      group member
    have allowedItem := items item (List.mem_cons_self ..)
    intro group member
    unfold Resolved.groupStep at member
    split at member
    · rename_i index _
      rw [List.modify_eq_set] at member
      rcases List.mem_or_eq_of_mem_set member with before | rfl
      · exact start group before
      · match h : found[index]? with
        | none => exact single item allowedItem
        | some previous => exact join previous item (start previous (List.mem_of_getElem? h)) allowedItem
    · rcases List.mem_append.mp member with before | fresh
      · exact start group before
      · rw [List.mem_singleton.mp fresh]
        exact single item allowedItem

/-- Grouping rule: for every context, query with {lit}`GROUP BY` terms and rows, every group of
{name}`Resolved.queryGroups` has a row, and each of its rows is one of the rows. Proof sketch:
{name}`Resolved.groups_eq_fold` and {name}`groupFold_property` with the property "nonempty and
within the rows". -/
theorem mem_queryGroups (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (grouped : query.groupBy ≠ []) (group : List (List Value)) (member : group ∈ Resolved.queryGroups context query rows) :
    group ≠ [] ∧ ∀ row ∈ group, row ∈ rows := by
  unfold Resolved.queryGroups at member
  rw [ite_eq_right (by simpa using grouped), Resolved.groups_eq_fold] at member
  exact groupFold_property _ (· ∈ rows) (fun group => group ≠ [] ∧ ∀ row ∈ group, row ∈ rows)
    (fun item inRows => ⟨List.cons_ne_nil _ _, fun _ h => List.mem_singleton.mp h ▸ inRows⟩)
    (fun group item ⟨_, within⟩ inRows => ⟨by simp, fun row h => by
      rcases List.mem_append.mp h with inGroup | last
      · exact within row inGroup
      · exact List.mem_singleton.mp last ▸ inRows⟩)
    rows [] (fun _ h => h) (by simp) group member

/-- Group-row rule: for every context, query without a deciding call and nonempty group, the
row of the group ({name}`Resolved.Query.groupRow`) is one of its rows. Proof sketch:
{name}`Resolved.Query.groupRow_none` gives the first row. -/
theorem groupRow_mem (context : Resolved.EvalContext) (query : Resolved.Query) (group : List (List Value))
    (plain : query.deciding = none) (nonempty : group ≠ []) : query.groupRow context group ∈ group := by
  rw [Resolved.Query.groupRow_none plain]
  cases group with
  | nil => exact absurd rfl nonempty
  | cons first rest => exact List.mem_cons_self ..

/-- Window rule: for every context, query, rows and row of {name}`Resolved.Query.results`, some
record of {name}`Resolved.Query.uniqueRecords` has the row as its output. Proof sketch:
{name}`Resolved.Query.results_window` shows the window as a drop and a take of the sorted
records, which {name}`Resolved.stableSort_perm` relates to the records. -/
theorem mem_results (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (row : List Value) (member : row ∈ query.results context rows) :
    ∃ record ∈ query.uniqueRecords context rows, record.1 = row := by
  rw [Resolved.Query.results_window] at member
  obtain ⟨record, inWindow, rfl⟩ := List.mem_map.mp member
  refine ⟨record, ?_, rfl⟩
  have sorted : record ∈ query.sortedRecords context rows := by
    unfold Resolved.windowRows at inWindow
    split at inWindow
    · exact List.mem_of_mem_drop inWindow
    · exact List.mem_of_mem_drop (List.mem_of_mem_take inWindow)
  exact (Resolved.stableSort_perm _ _).mem_iff.mp sorted

/-- Keep-fold rule: for every test, items and start, each item of the fold that keeps an item
when the test fails is in the start or in the items. {name}`Resolved.distinctRecords` is such a
fold. Proof sketch: induction on the items. -/
theorem mem_keepFold {β : Type} (keep : List β → β → Bool) : ∀ (items start : List β) (item : β),
    item ∈ items.foldl (fun kept found => if keep kept found then kept else kept ++ [found]) start →
      item ∈ start ∨ item ∈ items
  | [], _, _, h => .inl h
  | head :: tail, start, item, h => by
    simp only [List.foldl_cons] at h
    rcases mem_keepFold keep tail _ item h with inStart | inTail
    · split at inStart
      · exact .inl inStart
      · rcases List.mem_append.mp inStart with inStart | single
        · exact .inl inStart
        · exact .inr (List.mem_cons.mpr (.inl (List.mem_singleton.mp single)))
    · exact .inr (List.mem_cons_of_mem _ inTail)

/-- Distinct rule: for every context, query that is no compound, rows and record of
{name}`Resolved.Query.uniqueRecords`, the record is a record of the query over the rows that
{lit}`WHERE` keeps ({name}`Resolved.records`, {name}`Resolved.filtered`), with or without
{lit}`DISTINCT`. Proof sketch: without {lit}`DISTINCT` the records are the same list; with it,
{name}`mem_keepFold`. -/
theorem mem_uniqueRecords (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (record : Resolved.Record) (single : query.compound = none)
    (member : record ∈ query.uniqueRecords context rows) :
    record ∈ Resolved.records context query (Resolved.filtered context query rows) := by
  unfold Resolved.Query.uniqueRecords at member
  rw [single] at member
  simp only at member
  split at member
  · exact (mem_keepFold _ _ [] record member).resolve_left (by simp)
  · exact member

/-- Alternatives rule: for every context, query without {lit}`ORDER BY`, {lit}`OFFSET` and
{lit}`LIMIT`, and rows, the possible results are the one result in normal form. The model
law {name}`Resolved.Query.possibleResults_unordered` states the same rule.
Proof sketch: the sort of no terms keeps the records; one tie group holds them all; the window
takes all of it. -/
theorem possibleResults_noWindow (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (orderBy : query.orderBy = []) (offset : query.offset = 0) (limit : query.limit = none) :
    query.possibleResults context rows = [Resolved.normalForm (query.results context rows)] := by
  have sorted : query.sortedRecords context rows = query.uniqueRecords context rows := by
    unfold Resolved.Query.sortedRecords
    exact Resolved.stableSort_of_total _ (by simp [orderBy, Resolved.compareSort]) _
  have results : query.results context rows = (query.uniqueRecords context rows).map Prod.fst := by
    rw [Resolved.Query.results_window]
    simp [offset, Resolved.Query.stop, limit, Resolved.windowRows, sorted]
  unfold Resolved.Query.possibleResults Resolved.Query.tieGroupRows
  rw [sorted]
  simp only [orderBy, List.map_nil]
  by_cases empty : query.uniqueRecords context rows = []
  · simp [empty, results, Resolved.tieGroups, Resolved.windowChoices, Resolved.choiceResults,
      Resolved.distinctLists, Resolved.normalForm, Resolved.stableSort]
  · rw [Resolved.tieGroups_nil_directions _ empty]
    simp [results, Resolved.windowChoices, offset, Resolved.Query.stop, limit,
      Resolved.groupChoices, Resolved.groupSlice, Resolved.windowRows, Resolved.choiceResults,
      Resolved.distinctLists]

#print axioms mem_records_scalar
#print axioms mem_records_aggregate
#print axioms groupFold_property
#print axioms mem_queryGroups
#print axioms groupRow_mem
#print axioms mem_results
#print axioms mem_keepFold
#print axioms mem_uniqueRecords
#print axioms possibleResults_noWindow

end SelectAutomation
