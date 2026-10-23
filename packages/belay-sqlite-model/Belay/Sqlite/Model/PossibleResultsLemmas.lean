import Belay.Sqlite.Model.PossibleResults

set_option doc.verso true

/-! The lemmas of lists that the laws of the results that SQLite may give use
({lit}`PossibleResultsLaws.lean`): windows over lists, the ways to choose items, lists without
repetitions, the length of the normal form, and choices of one item of each list. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every window and lists, the window over two lists one after the other is the window over
the first, then the window moved by the first's length over the second. Proof sketch: unfold the
window into drop and take over the append, and match the counts by arithmetic. -/
theorem windowRows_append (start : Nat) (stop : Option Nat) (first second : List α) :
    windowRows start stop (first ++ second) =
      windowRows start stop first ++ windowRows (start - first.length) (stop.map (· - first.length)) second := by
  cases stop with
  | none => simp [windowRows, List.drop_append]
  | some stop =>
    simp only [windowRows, List.drop_append, List.take_append, List.length_drop, Option.map_some]
    congr 2 <;> omega

/-- For every window, function and list, the window commutes with mapping the items. Proof
sketch: drop and take commute with map. -/
theorem windowRows_map (start : Nat) (stop : Option Nat) (f : α → β) (items : List α) :
    windowRows start stop (items.map f) = (windowRows start stop items).map f := by
  cases stop <;> simp [windowRows, List.map_take, List.map_drop]

/-- For every window and list, the window is a sublist of the list. Proof sketch: a take of a
drop is a sublist of the drop, which is a sublist of the list. -/
theorem windowRows_sublist (start : Nat) (stop : Option Nat) (items : List α) :
    (windowRows start stop items).Sublist items := by
  cases stop with
  | none => exact List.drop_sublist _ _
  | some stop => exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

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

/-- For every count, list and choice of the count's items, the choice has the count's length.
Proof sketch: induction on the count and the list, following {name}`choose`. -/
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

/-- For every order, item and list, inserting the item adds one to the length. Proof sketch:
induction on the list, following {name}`insertStable`. -/
theorem insertStable_length (le : α → α → Bool) (item : α) : ∀ items : List α,
    (insertStable le item items).length = items.length + 1
  | [] => rfl
  | head :: tail => by
    unfold insertStable
    split <;> simp [insertStable_length le item tail]

/-- For every rows, the normal form has as many rows ({name}`normalForm`). Proof sketch: each
step of the fold of {name}`stableSort` adds one row ({name}`insertStable_length`). -/
theorem normalForm_length (rows : List (List Value)) : (normalForm rows).length = rows.length := by
  unfold normalForm stableSort
  suffices ∀ (sorted : List (List Value)), (rows.foldl (fun sorted item => insertStable _ item sorted) sorted).length =
      sorted.length + rows.length from by simpa using this []
  induction rows with
  | nil => simp
  | cons head rest ih => intro sorted; simp only [List.foldl_cons, ih, insertStable_length]; simp; omega

/-- For every window, position and group, the normal form of the rows that the window takes of
the group is one of the group's choices ({name}`groupChoices`). Proof sketch: the slice is a
sublist of the group; when it is as long, it is the group, else it is one of the ways to choose
({name}`mem_choose`), which the removal of repetitions keeps. -/
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
window takes of it. Proof sketch: the normal form keeps the length, and so does each way to
choose ({name}`length_of_mem_choose`). -/
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
result of the lists ({name}`choiceResults`). Proof sketch: induction on the pairing; the head's
choice is one of the first list's, and the rest follow. -/
theorem flatten_mem_choiceResults : ∀ {chosen : List (List (List Value))} {choices : List (List (List (List Value)))},
    Paired (· ∈ ·) chosen choices → chosen.flatten ∈ choiceResults choices
  | [], [], .nil => by simp [choiceResults]
  | _ :: _, _ :: _, .cons head rest => by
    simp only [choiceResults, List.flatten_cons, List.mem_flatMap, List.mem_map]
    exact ⟨_, head, _, flatten_mem_choiceResults rest, rfl⟩

/-- For every lists of choices whose choices have the lengths, each result has the sum of the
lengths as its length. Proof sketch: induction on the pairing; a result is a choice of the first
list followed by a result of the rest. -/
theorem length_of_mem_choiceResults : ∀ {choices : List (List (List (List Value)))} {lengths : List Nat},
    Paired (fun group length => ∀ chosen ∈ group, chosen.length = length) choices lengths →
      ∀ result ∈ choiceResults choices, result.length = lengths.sum
  | [], [], .nil, result, member => by simp [choiceResults] at member; simp [member]
  | _ :: _, _ :: _, .cons head rest, result, member => by
    simp only [choiceResults, List.mem_flatMap, List.mem_map] at member
    obtain ⟨chosen, inner, later, laterMember, rfl⟩ := member
    simp [head chosen inner, length_of_mem_choiceResults rest later laterMember]

end Belay.Sqlite.Model.Resolved
