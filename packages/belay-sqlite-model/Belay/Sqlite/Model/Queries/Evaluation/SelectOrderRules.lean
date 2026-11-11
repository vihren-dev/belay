import Belay.Sqlite.Model.Queries.Evaluation.SelectWindowRules

set_option doc.verso true

/-! The rules of the {lit}`order` and {lit}`window` phases of a query (ADR 0027, D1): every result
that the model permits ({name}`Belay.Sqlite.Model.Resolved.Query.possibleResults`) is the rows of
records in the order of the {lit}`ORDER BY` terms, which compare their sort values, not their
result rows: a sort key need not be a result column. The records are a permutation of a sublist
of the query's records. Records that the terms do not separate can come in any order, and a window
that cuts their tie group can take any of them, so tied rows need not be the same. The rules that
depend on the window ({lit}`OFFSET` and {lit}`LIMIT`) are in the module
{lit}`Belay.Sqlite.Model.SelectWindowOrderRules`. -/

namespace Belay.Sqlite.Model.Resolved

/-- Permutation-lift rule: for every function, list and permutation of the list's images, some
permutation of the list has the permutation as its images. Proof sketch: induction on the
permutation's items; the first item is the image of some item of the list, which moves to the
front. -/
theorem exists_perm_map_eq {α β : Type} (f : α → β) :
    ∀ {images : List β} {items : List α}, images.Perm (items.map f) → ∃ moved : List α, moved.Perm items ∧ moved.map f = images
  | [], items, perm => ⟨[], by simp_all, rfl⟩
  | image :: rest, items, perm => by
    obtain ⟨item, member, rfl⟩ := List.mem_map.mp (perm.subset (List.mem_cons_self ..))
    obtain ⟨before, after, rfl⟩ := List.append_of_mem member
    have restPerm : rest.Perm ((before ++ after).map f) :=
      (perm.trans (by simp)).cons_inv
    obtain ⟨moved, movedPerm, images⟩ := exists_perm_map_eq f restPerm
    exact ⟨item :: moved, ((movedPerm.cons item).trans List.perm_middle.symm), by simp [images]⟩

/-- Tie rule: for every directions and records, every two records of one tie group
({name}`tieGroups`) compare equal by the directions ({name}`compareSort`). Proof sketch: induction
on the records; a record joins a group when it compares equal to the group's first record, and
equality under a total order is symmetric and transitive. -/
theorem tieGroups_eq (directions : List (Bool × Collation)) : ∀ (records : List Record),
    ∀ group ∈ tieGroups directions records, ∀ a ∈ group, ∀ b ∈ group, compareSort directions a.2 b.2 = .eq
  | [] => by simp [tieGroups]
  | record :: rest => by
    have := compareSort_transCmp directions
    have ih := tieGroups_eq directions rest
    unfold tieGroups
    split
    · rename_i first group groups same
      rw [same] at ih
      split
      · rename_i joins
        have head : compareSort directions record.2 first.2 = .eq := by simpa using joins
        have old := ih _ (List.mem_cons_self ..)
        have toRecord : ∀ b ∈ first :: group, compareSort directions record.2 b.2 = .eq :=
          fun b member => Std.TransCmp.eq_trans head (old first (List.mem_cons_self ..) b member)
        intro other inGroups a inA b inB
        rcases List.mem_cons.mp inGroups with rfl | later
        · rcases List.mem_cons.mp inA with isRecord | laterA
          · rcases List.mem_cons.mp inB with isRecordB | laterB
            · rw [isRecord, isRecordB]
              exact Std.ReflCmp.compare_self
            · rw [isRecord]
              exact toRecord b laterB
          · rcases List.mem_cons.mp inB with isRecordB | laterB
            · rw [isRecordB]
              exact Std.OrientedCmp.eq_comm.mp (toRecord a laterA)
            · exact old a laterA b laterB
        · exact ih other (List.mem_cons_of_mem _ later) a inA b inB
      · intro other inGroups a inA b inB
        rcases List.mem_cons.mp inGroups with rfl | later
        · simp only [List.mem_singleton] at inA inB
          rw [inA, inB]
          exact Std.ReflCmp.compare_self
        · exact ih other later a inA b inB
    · rename_i groups same
      rw [same] at ih
      intro other inGroups a inA b inB
      rcases List.mem_cons.mp inGroups with rfl | later
      · simp only [List.mem_singleton] at inA inB
        rw [inA, inB]
        exact Std.ReflCmp.compare_self
      · exact ih other (List.mem_cons_of_mem _ later) a inA b inB
    · intro other inGroups a inA b inB
      simp only [List.mem_singleton] at inGroups
      subst inGroups
      simp only [List.mem_singleton] at inA inB
      rw [inA, inB]
      exact Std.ReflCmp.compare_self

/-- Ordered-choice rule: for every relation, window, position and groups of records whose records,
one after the other, are in order by the relation, and in each of which every two records are in
order both ways, each result of the choices of the groups' rows ({name}`choiceResults`,
{name}`windowChoices`) is the rows of records that are in order by the relation and are a
permutation of a sublist of the groups' records. Proof sketch: induction on the groups; the
choice of a group is a permutation of a sublist of its rows ({name}`exists_sublist_of_mem_groupChoices`),
which lifts to its records ({name}`exists_perm_map_eq`); records of one group are in order in any
order, and of an earlier group before every record of a later group. -/
theorem exists_ordered_of_mem_choiceResults (inOrder : Record → Record → Prop) (start : Nat) (stop : Option Nat) :
    ∀ (position : Nat) (groups : List (List Record)), groups.flatten.Pairwise inOrder →
      (∀ group ∈ groups, ∀ a ∈ group, ∀ b ∈ group, inOrder a b) →
      ∀ result ∈ choiceResults (windowChoices start stop position (groups.map (·.map Prod.fst))),
        ∃ ordered : List Record, (∃ picked : List Record, picked.Sublist groups.flatten ∧ ordered.Perm picked) ∧
          ordered.Pairwise inOrder ∧ result = ordered.map Prod.fst
  | _, [], _, _, result, member => by
    simp [windowChoices, choiceResults] at member
    exact ⟨[], ⟨[], .slnil, .nil⟩, .nil, member⟩
  | position, group :: groups, sorted, ties, result, member => by
    simp only [List.map_cons, windowChoices, choiceResults, List.mem_flatMap, List.mem_map] at member
    obtain ⟨chosen, inner, later, laterMember, rfl⟩ := member
    rw [List.flatten_cons, List.pairwise_append] at sorted
    obtain ⟨-, restSorted, across⟩ := sorted
    obtain ⟨pickedRows, rowsSublist, chosenPerm⟩ := exists_sublist_of_mem_groupChoices inner
    obtain ⟨picked, pickedSublist, rfl⟩ := List.sublist_map_iff.mp rowsSublist
    obtain ⟨moved, movedPerm, rfl⟩ := exists_perm_map_eq Prod.fst chosenPerm
    obtain ⟨ordered, ⟨restPicked, restSublist, restPerm⟩, orderedSorted, rfl⟩ :=
      exists_ordered_of_mem_choiceResults inOrder start stop _ groups restSorted
        (fun other member => ties other (List.mem_cons_of_mem _ member)) later (by simpa using laterMember)
    have inGroup : ∀ a ∈ moved, a ∈ group := fun a member => pickedSublist.subset (movedPerm.subset member)
    refine ⟨moved ++ ordered, ⟨picked ++ restPicked, pickedSublist.append restSublist, movedPerm.append restPerm⟩,
      List.pairwise_append.mpr ⟨?_, orderedSorted, fun a inMoved b inOrdered => ?_⟩, by simp⟩
    · exact List.pairwise_of_forall_mem_list fun a inA b inB =>
        ties group (List.mem_cons_self ..) a (inGroup a inA) b (inGroup b inB)
    · exact across a (inGroup a inMoved) b (restSublist.subset (restPerm.subset inOrdered))

/-- Order rule: for every context, query, rows and result that the model permits
({name}`Query.possibleResults`), the result is the rows of some records that:
- are a permutation of a sublist of the query's records ({name}`Query.uniqueRecords`);
- are in order by the {lit}`ORDER BY` terms: each record's sort values compare as at most every
  later record's ({name}`compareSort`).

This holds for every {lit}`OFFSET` and {lit}`LIMIT`. Without {lit}`ORDER BY` every two records are in
order, so the rule then says only the first point. Proof sketch: the sorted records are in order
({name}`sort_sorted`), their tie groups compare equal inside ({name}`tieGroups_eq`), so each result
of the choices is in order ({name}`exists_ordered_of_mem_choiceResults`); the sorted records are a
permutation of the records. -/
theorem Query.exists_sorted_of_mem_possibleResults {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (member : result ∈ query.possibleResults context rows) :
    ∃ ordered : List Record,
      (∃ picked : List Record, picked.Sublist (query.uniqueRecords context rows) ∧ ordered.Perm picked) ∧
        ordered.Pairwise (fun a b =>
          (compareSort (query.orderBy.map fun term => (term.descending, term.collation)) a.2 b.2).isLE) ∧
        result = ordered.map Prod.fst := by
  have := compareSort_transCmp (query.orderBy.map fun term => (term.descending, term.collation))
  have flatten := tieGroups_flatten (query.orderBy.map fun term => (term.descending, term.collation))
    (query.sortedRecords context rows)
  obtain ⟨ordered, ⟨picked, sublist, perm⟩, sorted, rfl⟩ :=
    exists_ordered_of_mem_choiceResults _ query.offset query.stop 0 _ (by rw [flatten]; exact sort_sorted _ _)
      (fun group inGroups a inA b inB => by
        rw [tieGroups_eq _ _ group inGroups a inA b inB]; rfl)
      result (mem_distinctLists.mp member)
  rw [flatten] at sublist
  obtain ⟨other, otherPerm, otherSublist⟩ := List.exists_perm_sublist sublist (stableSort_perm _ _)
  exact ⟨ordered, ⟨other, otherSublist, perm.trans otherPerm.symm⟩, sorted, rfl⟩

end Belay.Sqlite.Model.Resolved
