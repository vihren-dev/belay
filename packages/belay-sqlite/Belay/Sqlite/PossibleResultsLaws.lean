import Belay.Sqlite.PossibleResultsLemmas

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
sorted records. Proof sketch: unfold both and compare the take of {lit}`LIMIT` with the window's
end, case by case on {lit}`LIMIT`. -/
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

/-- For every window, position and groups, the normal form of each slice is a choice of its
group, slice by slice. Proof sketch: induction on the groups with
{name}`normalForm_slice_mem`. -/
theorem slices_forall₂ (start : Nat) (stop : Option Nat) : ∀ (position : Nat) (groups : List (List (List Value))),
    Paired (· ∈ ·) ((windowSlices start stop position groups).map normalForm) (windowChoices start stop position groups)
  | _, [] => .nil
  | position, group :: groups => .cons (normalForm_slice_mem start stop position group)
      (slices_forall₂ start stop (position + group.length) groups)

/-- For every window, position and groups, the choices of each group have the length of its
slice. Proof sketch: induction on the groups with {name}`length_of_mem_groupChoices`. -/
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
