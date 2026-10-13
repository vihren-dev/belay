import Belay.Sqlite.QueryEval

set_option doc.verso true

/-! The laws of query evaluation that ADR 0012 requires: the filter keeps exactly
the rows whose condition is true, the {lit}`ORDER BY` result is a sorted permutation
of its input, the window has the length that {lit}`OFFSET` and {lit}`LIMIT` give, and
{lit}`COUNT(*)` counts the rows of a group. -/

namespace Belay.Sqlite.Resolved

/-- For every transitive comparison and every key function, comparing the keys is
again a transitive comparison. -/
theorem transCmp_on {cmp : β → β → Ordering} [Std.TransCmp cmp] (key : α → β) :
    Std.TransCmp (fun a b => cmp (key a) (key b)) where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans first second := Std.TransCmp.isLE_trans first second

/-- For both directions, {name}`compareTerm` is a transitive comparison: ascending
is {name}`compareValues`, descending is its opposite. -/
theorem compareTerm_transCmp (descending : Bool) : Std.TransCmp (compareTerm descending) := by
  cases descending
  · have equal : compareTerm false = compareValues := by funext a b; simp [compareTerm]
    rw [equal]; exact inferInstance
  · have equal : compareTerm true = fun a b => compareValues b a := by funext a b; simp [compareTerm]
    rw [equal]; exact Std.TransCmp.opposite

/-- For every list of directions, {name}`compareSort` is a transitive comparison of
lists of sort values. The proof inducts over the directions: each step is the
lexicographic combination of the first term and the rest, by the core instance. -/
theorem compareSort_transCmp : ∀ directions : List Bool, Std.TransCmp (compareSort directions)
  | [] => { eq_swap := by simp [compareSort], isLE_trans := by simp [compareSort] }
  | descending :: directions => by
    have := compareTerm_transCmp descending
    have := compareSort_transCmp directions
    have := transCmp_on (cmp := compareTerm descending) (fun values : List Value => values.headD .null)
    have := transCmp_on (cmp := compareSort directions) (fun values : List Value => values.tail)
    have equal : compareSort (descending :: directions) = compareLex
        (fun a b => compareTerm descending (a.headD .null) (b.headD .null))
        (fun a b => compareSort directions a.tail b.tail) := by
      funext a b; simp [compareSort, compareLex]
    rw [equal]; exact inferInstance

/-- For every list of directions and records, the sorted records are a permutation
of the records: the sort neither adds, drops nor repeats a record. -/
theorem sort_perm (directions : List Bool) (items : List Record) :
    (items.mergeSort fun a b => (compareSort directions a.2 b.2).isLE).Perm items :=
  List.mergeSort_perm _ _

/-- For every list of directions and records, the sorted records are in order:
each record compares as less than or equal to every later record by the
{lit}`ORDER BY` terms. The proof uses the core lemma for {lit}`mergeSort` with the
transitivity and totality of {name}`compareSort`. -/
theorem sort_sorted (directions : List Bool) (items : List Record) :
    (items.mergeSort fun a b => (compareSort directions a.2 b.2).isLE).Pairwise
      fun a b => (compareSort directions a.2 b.2).isLE := by
  have := compareSort_transCmp directions
  apply List.pairwise_mergeSort
  · intro a b c first second
    exact Std.TransCmp.isLE_trans first second
  · intro a b
    rw [Std.OrientedCmp.eq_swap (cmp := compareSort directions) (a := b.2)]
    cases compareSort directions a.2 b.2 <;> rfl

/-- For every query and list of rows, a row is in {name}`filtered` exactly when it
is in the list and the {lit}`WHERE` condition, if any, is true for it. -/
theorem mem_filtered (query : Query) (rows : List (List Value)) (row : List Value) :
    row ∈ filtered query rows ↔ row ∈ rows ∧ query.filter.all (fun condition => truthy (condition.eval row)) = true := by
  simp [filtered]

/-- For every list of records, offset and limit, the window keeps the records after
the first {lit}`offset`, at most {lit}`limit` of them: its length is the smaller of
the limit and the number of records after the offset. -/
theorem window_length (items : List Record) (offset limit : Nat) :
    ((items.drop offset).take limit).length = min limit (items.length - offset) := by
  simp

/-- For every group of rows, {lit}`COUNT(*)` is the number of rows in the group. -/
theorem countRows_eval (group : List (List Value)) :
    Aggregate.countRows.eval group = .integer group.length := rfl

end Belay.Sqlite.Resolved
