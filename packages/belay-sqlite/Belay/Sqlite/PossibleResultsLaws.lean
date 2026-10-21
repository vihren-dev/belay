import Belay.Sqlite.PossibleResults

set_option doc.verso true

/-! The laws of the results that SQLite may give (ADR 0018, D6): the one result that the model
computes, {name}`Belay.Sqlite.Resolved.Query.results`, is the rows that the window takes of each
tie group, so with each group in normal form it is in the list
({lit}`Query.normalResult_mem`); every result of the list has as many
rows; and the list is never empty. The corpora check {lit}`Query.results` against SQLite, so they
check one element of the list. -/

namespace Belay.Sqlite.Resolved

/-- For every directions and records, the tie groups of the records, one after the other, are
the records. Proof sketch: induction on the records; each record joins the first group or
starts one. -/
theorem tieGroups_flatten (directions : List (Bool × Collation)) : ∀ records : List Record,
    (tieGroups directions records).flatten = records
  | [] => rfl
  | record :: rest => by
    have ih := tieGroups_flatten directions rest
    unfold tieGroups
    split
    · rename_i first group groups same
      rw [same] at ih
      split <;> simp_all
    · rename_i groups same
      rw [same] at ih
      simp_all
    · rename_i same
      rw [same] at ih
      simp_all

/-- For every window and lists, the window over two lists one after the other is the window over
the first, then the window moved by the first's length over the second. -/
theorem windowRows_append (start : Nat) (stop : Option Nat) (first second : List α) :
    windowRows start stop (first ++ second) =
      windowRows start stop first ++ windowRows (start - first.length) (stop.map (· - first.length)) second := by
  cases stop with
  | none => simp [windowRows, List.drop_append]
  | some stop =>
    simp only [windowRows, List.drop_append, List.take_append, List.length_drop, Option.map_some]
    congr 2 <;> omega

/-- For every window, function and list, the window commutes with mapping the items. -/
theorem windowRows_map (start : Nat) (stop : Option Nat) (f : α → β) (items : List α) :
    windowRows start stop (items.map f) = (windowRows start stop items).map f := by
  cases stop <;> simp [windowRows, List.map_take, List.map_drop]

/-- For every window and list, the window is a sublist of the list. -/
theorem windowRows_sublist (start : Nat) (stop : Option Nat) (items : List α) :
    (windowRows start stop items).Sublist items := by
  cases stop with
  | none => exact List.drop_sublist _ _
  | some stop => exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

/-- For every window, position and groups, the slices that the window takes of the groups, one
after the other, are the window, moved by the position, over the groups one after the other.
Proof sketch: induction on the groups with {name}`windowRows_append`. -/
theorem windowSlices_flatten (start : Nat) (stop : Option Nat) :
    ∀ (position : Nat) (groups : List (List (List Value))),
      (windowSlices start stop position groups).flatten =
        windowRows (start - position) (stop.map (· - position)) groups.flatten
  | _, [] => by cases stop <;> simp [windowSlices, windowRows]
  | position, group :: groups => by
    simp only [windowSlices, List.flatten_cons, windowRows_append, windowSlices_flatten start stop (position + group.length),
      groupSlice, Option.map_map]
    congr 2
    · omega
    · cases stop <;> simp [Function.comp_def, Nat.sub_sub]

/-- For every context, query and rows, {name}`Query.results` is the window of the query over its
sorted records. -/
theorem Query.results_window (context : EvalContext) (query : Query) (rows : List (List Value)) :
    query.results context rows = (windowRows query.offset query.stop (query.sortedRecords context rows)).map Prod.fst := by
  unfold Query.results Query.stop Query.sortedRecords
  cases query.limit <;> simp [windowRows]

/-- For every context, query and rows, the slices that the window takes of the tie groups, one
after the other, are {name}`Query.results`. Proof sketch: the groups are the sorted records
({name}`tieGroups_flatten`), and the window over them splits into the slices
({name}`windowSlices_flatten`). -/
theorem Query.slices_results (context : EvalContext) (query : Query) (rows : List (List Value)) :
    (windowSlices query.offset query.stop 0 (query.tieGroupRows context rows)).flatten = query.results context rows := by
  rw [windowSlices_flatten, Query.results_window, Query.tieGroupRows, ← List.map_flatten, tieGroups_flatten, ← windowRows_map]
  cases query.stop <;> simp

/-- For every list and sublist of it, the sublist is one of the ways to choose as many items of
the list ({name}`choose`). Proof sketch: induction on the sublist relation. -/
theorem mem_choose {sub items : List α} (sublist : sub.Sublist items) : sub ∈ choose sub.length items := by
  induction sublist with
  | slnil => simp [choose]
  | @cons first rest item _ ih =>
    cases first with
    | nil => simp [choose]
    | cons head tail => simp only [List.length_cons, choose, List.mem_append, List.mem_map] at ih ⊢; exact .inr ih
  | @cons_cons first rest item _ ih =>
    simp only [List.length_cons, choose, List.mem_append, List.mem_map]; exact .inl ⟨_, ih, rfl⟩

/-- For every count, list and choice of the count's items, the choice has the count's length. -/
theorem length_of_mem_choose : ∀ {count : Nat} {items chosen : List α}, chosen ∈ choose count items → chosen.length = count
  | 0, _, chosen, member => by simp [choose] at member; simp [member]
  | _ + 1, [], _, member => by simp [choose] at member
  | count + 1, item :: rest, chosen, member => by
    simp only [choose, List.mem_append, List.mem_map] at member
    rcases member with ⟨tail, inner, rfl⟩ | inner
    · simp [length_of_mem_choose inner]
    · exact length_of_mem_choose inner

/-- For every list with lawful equality and item, the item is in the list without its
repetitions ({name}`distinctLists`) exactly when it is in the list. Proof sketch: induction on
the list; the filter removes only copies of the head. -/
theorem mem_distinctLists [BEq α] [LawfulBEq α] {item : α} : ∀ {items : List α},
    item ∈ distinctLists items ↔ item ∈ items
  | [] => by simp [distinctLists]
  | head :: rest => by
    have ih := @mem_distinctLists α _ _ item rest
    by_cases same : item = head
    · subst same; simp [distinctLists]
    · simp [distinctLists, List.mem_filter, ih, same]

/-- For every order, item and list, inserting the item adds one to the length. -/
theorem insertStable_length (le : α → α → Bool) (item : α) : ∀ items : List α,
    (insertStable le item items).length = items.length + 1
  | [] => rfl
  | head :: tail => by
    unfold insertStable
    split <;> simp [insertStable_length le item tail]

/-- For every rows, the normal form has as many rows ({name}`normalForm`). -/
theorem normalForm_length (rows : List (List Value)) : (normalForm rows).length = rows.length := by
  unfold normalForm stableSort
  suffices ∀ (sorted : List (List Value)), (rows.foldl (fun sorted item => insertStable _ item sorted) sorted).length =
      sorted.length + rows.length from by simpa using this []
  induction rows with
  | nil => simp
  | cons head rest ih => intro sorted; simp only [List.foldl_cons, ih, insertStable_length]; simp; omega

/-- For every window, position and group, the normal form of the rows that the window takes of
the group is one of the group's choices ({name}`groupChoices`). -/
theorem normalForm_slice_mem (start : Nat) (stop : Option Nat) (position : Nat) (group : List (List Value)) :
    normalForm (groupSlice start stop position group) ∈ groupChoices start stop position group := by
  have sub : (groupSlice start stop position group).Sublist group := windowRows_sublist _ _ _
  unfold groupChoices
  split
  · rename_i whole
    have same := sub.eq_of_length (by simpa using whole)
    simp [same]
  · exact mem_distinctLists.mpr (List.mem_map.mpr ⟨_, mem_choose sub, rfl⟩)

/-- For every window, position and group, each choice of the group has as many rows as the
window takes of it. -/
theorem length_of_mem_groupChoices {start : Nat} {stop : Option Nat} {position : Nat} {group chosen : List (List Value)}
    (member : chosen ∈ groupChoices start stop position group) :
    chosen.length = (groupSlice start stop position group).length := by
  unfold groupChoices at member
  split at member
  · rename_i whole
    simp only [List.mem_singleton] at member
    subst member
    simpa [normalForm_length] using (beq_iff_eq.mp whole).symm
  · obtain ⟨picked, inner, rfl⟩ := List.mem_map.mp (mem_distinctLists.mp member)
    rw [normalForm_length, length_of_mem_choose inner]

/-- Two lists of the same length whose items at each index are related. -/
inductive Paired (related : α → β → Prop) : List α → List β → Prop where
  /-- Two empty lists. -/
  | nil : Paired related [] []
  /-- Two related heads and two related tails. -/
  | cons {head : α} {other : β} {rest : List α} {others : List β} :
      related head other → Paired related rest others → Paired related (head :: rest) (other :: others)

/-- For every lists of choices and one choice of each, the choices one after the other are a
result of the lists ({name}`choiceResults`). -/
theorem flatten_mem_choiceResults : ∀ {chosen : List (List (List Value))} {choices : List (List (List (List Value)))},
    Paired (· ∈ ·) chosen choices → chosen.flatten ∈ choiceResults choices
  | [], [], .nil => by simp [choiceResults]
  | _ :: _, _ :: _, .cons head rest => by
    simp only [choiceResults, List.flatten_cons, List.mem_flatMap, List.mem_map]
    exact ⟨_, head, _, flatten_mem_choiceResults rest, rfl⟩

/-- For every lists of choices whose choices have the lengths, each result has the sum of the
lengths as its length. -/
theorem length_of_mem_choiceResults : ∀ {choices : List (List (List (List Value)))} {lengths : List Nat},
    Paired (fun group length => ∀ chosen ∈ group, chosen.length = length) choices lengths →
      ∀ result ∈ choiceResults choices, result.length = lengths.sum
  | [], [], .nil, result, member => by simp [choiceResults] at member; simp [member]
  | _ :: _, _ :: _, .cons head rest, result, member => by
    simp only [choiceResults, List.mem_flatMap, List.mem_map] at member
    obtain ⟨chosen, inner, later, laterMember, rfl⟩ := member
    simp [head chosen inner, length_of_mem_choiceResults rest later laterMember]

/-- For every window, position and groups, the normal form of each slice is a choice of its
group, slice by slice. -/
theorem slices_forall₂ (start : Nat) (stop : Option Nat) : ∀ (position : Nat) (groups : List (List (List Value))),
    Paired (· ∈ ·) ((windowSlices start stop position groups).map normalForm) (windowChoices start stop position groups)
  | _, [] => .nil
  | position, group :: groups => .cons (normalForm_slice_mem start stop position group)
      (slices_forall₂ start stop (position + group.length) groups)

/-- For every window, position and groups, the choices of each group have the length of its
slice. -/
theorem choices_lengths (start : Nat) (stop : Option Nat) : ∀ (position : Nat) (groups : List (List (List Value))),
    Paired (fun group length => ∀ chosen ∈ group, chosen.length = length)
      (windowChoices start stop position groups) ((windowSlices start stop position groups).map List.length)
  | _, [] => .nil
  | position, group :: groups => .cons (fun _ member => length_of_mem_groupChoices member)
      (choices_lengths start stop (position + group.length) groups)

/-- For every context, query and rows, the one result of the model ({name}`Query.results`) with
the rows of each tie group in normal form ({name}`Query.normalResult`) is a result that SQLite may
give ({name}`Query.possibleResults`). Proof sketch: each normalized slice is a choice of its group
({name}`normalForm_slice_mem`), so the slices one after the other are a result of the choices
({name}`flatten_mem_choiceResults`), which the removal of repetitions keeps. -/
theorem Query.normalResult_mem (context : EvalContext) (query : Query) (rows : List (List Value)) :
    query.normalResult context rows ∈ query.possibleResults context rows :=
  mem_distinctLists.mpr (flatten_mem_choiceResults (slices_forall₂ query.offset query.stop 0 (query.tieGroupRows context rows)))

/-- For every context, query, rows and result that SQLite may give, the result has as many rows
as the model's one result ({name}`Query.results`). Proof sketch: the choices of each group have
the length of its slice ({name}`choices_lengths`), and the slices one after the other are
{name}`Query.results` ({name}`Query.slices_results`). -/
theorem Query.possibleResults_length (context : EvalContext) (query : Query) (rows : List (List Value))
    (result : List (List Value)) (member : result ∈ query.possibleResults context rows) :
    result.length = (query.results context rows).length := by
  rw [← Query.slices_results, List.length_flatten]
  exact length_of_mem_choiceResults (choices_lengths query.offset query.stop 0 (query.tieGroupRows context rows)) result
    (mem_distinctLists.mp member)

/-- For every context, query and rows, SQLite may give at least one result. -/
theorem Query.possibleResults_ne_nil (context : EvalContext) (query : Query) (rows : List (List Value)) :
    query.possibleResults context rows ≠ [] :=
  List.ne_nil_of_mem (Query.normalResult_mem context query rows)

end Belay.Sqlite.Resolved
