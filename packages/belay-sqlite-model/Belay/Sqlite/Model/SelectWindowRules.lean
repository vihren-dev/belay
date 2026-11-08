import Belay.Sqlite.Model.PossibleResultsLaws
import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-! The rules of the result phase of a SELECT (ADR 0027 D1): every result that the model permits
({name}`Belay.Sqlite.Model.Resolved.Query.possibleResults`) is a permutation of a sublist of the
rows of the query's records ({name}`Belay.Sqlite.Model.Resolved.Query.uniqueRecords`), whatever
the {lit}`ORDER BY` terms and the window. So each row of a result is a row of a record, a row
occurs in a result at most as often as in the records, and a result has at most as many rows.
Without {lit}`OFFSET` and {lit}`LIMIT`, each result is a permutation of all the rows of the
records. The alternatives are those that the model represents: where SQLite's plan chooses the
row of a group, the model gives one row ({lit}`Query.groupRow`, ADR 0027 D4), so the rules do not
cover the results of the other rows. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every count, list and choice of the count's items ({name}`choose`), the choice is a
sublist of the list. Proof sketch: induction on the count and the list, following
{name}`choose`. -/
theorem sublist_of_mem_choose : ∀ {count : Nat} {items chosen : List α}, chosen ∈ choose count items → chosen.Sublist items
  | 0, _, chosen, member => by simp [choose] at member; subst member; exact List.nil_sublist _
  | _ + 1, [], _, member => by simp [choose] at member
  | count + 1, item :: rest, chosen, member => by
    simp only [choose, List.mem_append, List.mem_map] at member
    rcases member with ⟨tail, inner, rfl⟩ | inner
    · exact (sublist_of_mem_choose inner).cons_cons item
    · exact (sublist_of_mem_choose inner).cons item

/-- For every rows, the normal form ({name}`normalForm`) is a permutation of the rows. Proof sketch:
the normal form is a stable sort, which permutes its list ({name}`stableSort_perm`). -/
theorem normalForm_perm (rows : List (List Value)) : (normalForm rows).Perm rows := stableSort_perm _ _

/-- For every window, position, group and choice of the group ({name}`groupChoices`), the choice
is a permutation of a sublist of the group. Proof sketch: the choice is the normal form of the
group, or of one of the ways to choose its rows ({name}`sublist_of_mem_choose`). -/
theorem exists_sublist_of_mem_groupChoices {start : Nat} {stop : Option Nat} {position : Nat}
    {group chosen : List (List Value)} (member : chosen ∈ groupChoices start stop position group) :
    ∃ picked, picked.Sublist group ∧ chosen.Perm picked := by
  unfold groupChoices at member
  split at member
  · simp only [List.mem_singleton] at member
    exact ⟨group, List.Sublist.refl _, member ▸ normalForm_perm group⟩
  · obtain ⟨picked, inner, rfl⟩ := List.mem_map.mp (mem_distinctLists.mp member)
    exact ⟨picked, sublist_of_mem_choose inner, normalForm_perm picked⟩

/-- For every window, position, groups and result of the choices of the groups
({name}`choiceResults`, {name}`windowChoices`), the result is a permutation of a sublist of the
groups one after the other. Proof sketch: induction on the groups; a result is a choice of the
first group followed by a result of the rest, and sublists and permutations join
({name}`exists_sublist_of_mem_groupChoices`). -/
theorem exists_sublist_of_mem_choiceResults (start : Nat) (stop : Option Nat) :
    ∀ (position : Nat) (groups : List (List (List Value))),
      ∀ result ∈ choiceResults (windowChoices start stop position groups),
        ∃ picked, picked.Sublist groups.flatten ∧ result.Perm picked
  | _, [], result, member => by
    simp [windowChoices, choiceResults] at member
    exact ⟨[], List.Sublist.slnil, by simp [member]⟩
  | position, group :: groups, result, member => by
    simp only [windowChoices, choiceResults, List.mem_flatMap, List.mem_map] at member
    obtain ⟨chosen, inner, later, laterMember, rfl⟩ := member
    obtain ⟨first, firstSublist, firstPerm⟩ := exists_sublist_of_mem_groupChoices inner
    obtain ⟨rest, restSublist, restPerm⟩ :=
      exists_sublist_of_mem_choiceResults start stop (position + group.length) groups later laterMember
    exact ⟨first ++ rest, by simpa using firstSublist.append restSublist, firstPerm.append restPerm⟩

/-- For every context, query and rows, the tie groups of the sorted records, one after the
other, are the rows of the sorted records ({name}`Query.tieGroupRows`,
{name}`Query.sortedRecords`). Proof sketch: the rows of the groups are the rows of the groups'
records, and the groups one after the other are the records ({name}`tieGroups_flatten`). -/
theorem Query.tieGroupRows_flatten (context : EvalContext) (query : Query) (rows : List (List Value)) :
    (query.tieGroupRows context rows).flatten = (query.sortedRecords context rows).map Prod.fst := by
  rw [Query.tieGroupRows, ← List.map_flatten, tieGroups_flatten]

/-- Result rule: for every context, query, rows and result that the model permits
({name}`Query.possibleResults`), some sublist of the rows of the query's records
({name}`Query.uniqueRecords`) has the result as a permutation. This holds for every
{lit}`ORDER BY`, {lit}`OFFSET` and {lit}`LIMIT`. Proof sketch: the result is a permutation of a
sublist of the tie groups ({name}`exists_sublist_of_mem_choiceResults`), which are the sorted
records, a permutation of the records ({name}`stableSort_perm`); a sublist of a permutation is a
permutation of a sublist. -/
theorem Query.exists_sublist_of_mem_possibleResults {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (member : result ∈ query.possibleResults context rows) :
    ∃ picked, picked.Sublist ((query.uniqueRecords context rows).map Prod.fst) ∧ result.Perm picked := by
  obtain ⟨picked, sublist, perm⟩ :=
    exists_sublist_of_mem_choiceResults query.offset query.stop 0 _ result (mem_distinctLists.mp member)
  rw [Query.tieGroupRows_flatten] at sublist
  have sorted : (query.sortedRecords context rows).Perm (query.uniqueRecords context rows) := stableSort_perm _ _
  obtain ⟨other, otherPerm, otherSublist⟩ := List.exists_perm_sublist sublist (sorted.map Prod.fst)
  exact ⟨other, otherSublist, perm.trans otherPerm.symm⟩

/-- For every context, query, rows, result that the model permits and row of the result, the row
is the row of a record of the query ({name}`Query.uniqueRecords`). Proof sketch: a permutation keeps
the members, and a sublist has only members of its list
({name}`Query.exists_sublist_of_mem_possibleResults`). -/
theorem Query.mem_of_mem_possibleResults {context : EvalContext} {query : Query} {rows result : List (List Value)}
    (member : result ∈ query.possibleResults context rows) {row : List Value} (inResult : row ∈ result) :
    row ∈ (query.uniqueRecords context rows).map Prod.fst := by
  obtain ⟨picked, sublist, perm⟩ := Query.exists_sublist_of_mem_possibleResults member
  exact sublist.subset (perm.mem_iff.mp inResult)

/-- For every context, query, rows, result that the model permits and row, the result has the row
at most as often as the rows of the query's records ({name}`Query.uniqueRecords`). Proof sketch: a
permutation keeps the counts, and a sublist has at most the counts of its list. -/
theorem Query.count_le_of_mem_possibleResults {context : EvalContext} {query : Query} {rows result : List (List Value)}
    (member : result ∈ query.possibleResults context rows) (row : List Value) :
    result.count row ≤ ((query.uniqueRecords context rows).map Prod.fst).count row := by
  obtain ⟨picked, sublist, perm⟩ := Query.exists_sublist_of_mem_possibleResults member
  exact perm.count_eq row ▸ sublist.count_le row

/-- For every context, query, rows and result that the model permits, the result has at most as
many rows as the query has records ({name}`Query.uniqueRecords`). Proof sketch: a permutation keeps
the length, and a sublist is at most as long as its list. -/
theorem Query.length_le_of_mem_possibleResults {context : EvalContext} {query : Query} {rows result : List (List Value)}
    (member : result ∈ query.possibleResults context rows) :
    result.length ≤ (query.uniqueRecords context rows).length := by
  obtain ⟨picked, sublist, perm⟩ := Query.exists_sublist_of_mem_possibleResults member
  simpa [perm.length_eq] using sublist.length_le

/-- Result rule without a window: for every context, query with {lit}`OFFSET` 0 and no
{lit}`LIMIT`, rows and result that the model permits, the result is a permutation of the rows of
all the query's records ({name}`Query.uniqueRecords`). This holds for every {lit}`ORDER BY`.
Proof sketch: the result is a permutation of a sublist of the records' rows
({name}`Query.exists_sublist_of_mem_possibleResults`) and has as many rows as the model's one
result ({name}`Query.possibleResults_length`), which without a window has all the records; a
sublist as long as its list is the list. -/
theorem Query.perm_of_mem_possibleResults {context : EvalContext} {query : Query} {rows result : List (List Value)}
    (offset : query.offset = 0) (limit : query.limit = none) (member : result ∈ query.possibleResults context rows) :
    result.Perm ((query.uniqueRecords context rows).map Prod.fst) := by
  obtain ⟨picked, sublist, perm⟩ := Query.exists_sublist_of_mem_possibleResults member
  have sorted : (query.sortedRecords context rows).Perm (query.uniqueRecords context rows) := stableSort_perm _ _
  have length : result.length = (query.uniqueRecords context rows).length := by
    rw [Query.possibleResults_length context query rows result member, Query.results_window]
    simp [offset, Query.stop, limit, windowRows, sorted.length_eq]
  exact sublist.eq_of_length (by simp [← perm.length_eq, length]) ▸ perm

/-- For every order that holds between any two items, inserting an item puts it at the end of the list. Proof
sketch: induction on the list; each leading item is at most the new item. -/
theorem insertStable_of_total {α : Type} (le : α → α → Bool) (always : ∀ a b, le a b = true) (item : α) :
    ∀ items : List α, insertStable le item items = items ++ [item]
  | [] => rfl
  | head :: tail => by simp [insertStable, always, insertStable_of_total le always item tail]

/-- For every order that holds between any two items, the stable sort keeps the list as it is. Proof sketch:
each step of the fold appends the next item ({name}`insertStable_of_total`). -/
theorem stableSort_of_total {α : Type} (le : α → α → Bool) (always : ∀ a b, le a b = true) (items : List α) :
    stableSort le items = items := by
  have step : ∀ (sorted items : List α), items.foldl (fun sorted item => insertStable le item sorted) sorted =
      sorted ++ items := by
    intro sorted items
    induction items generalizing sorted with
    | nil => simp
    | cons head tail ih => rw [List.foldl_cons, insertStable_of_total le always, ih, List.append_assoc,
        List.singleton_append]
  simpa [stableSort] using step [] items

end Belay.Sqlite.Model.Resolved
