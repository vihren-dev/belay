import Belay.Sqlite.QueryEval

set_option doc.verso true

/-! The laws of query evaluation that ADR 0012 requires: the filter keeps exactly
the rows whose condition is true, the {lit}`ORDER BY` result is a sorted permutation
of its input, the window has the length that {lit}`OFFSET` and {lit}`LIMIT` give, and
{lit}`COUNT(*)` counts the rows of a group. -/

namespace Belay.Sqlite.Resolved

/-- For every transitive comparison and every key function, comparing the keys is
again a transitive comparison. The proof applies the orientation and transitivity
laws of the original comparison to the keys of the compared values. -/
theorem transCmp_on {cmp : β → β → Ordering} [Std.TransCmp cmp] (key : α → β) :
    Std.TransCmp (fun a b => cmp (key a) (key b)) where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans first second := Std.TransCmp.isLE_trans first second

/-- For both directions and every collation, {name}`compareTerm` is a transitive
comparison: ascending, it is {name}`Collation.compare`; descending, its opposite. -/
theorem compareTerm_transCmp (descending : Bool) (collation : Collation) :
    Std.TransCmp (compareTerm descending collation) := by
  cases descending
  · have equal : compareTerm false collation = collation.compare := by funext a b; simp [compareTerm]
    rw [equal]; exact inferInstance
  · have equal : compareTerm true collation = fun a b => collation.compare b a := by
      funext a b; simp [compareTerm]
    rw [equal]; exact Std.TransCmp.opposite

/-- For every list of directions with collations, {name}`compareSort` is a transitive
comparison of lists of sort values. The proof inducts over the terms: each step is the
lexicographic combination of the first term and the rest, by the core instance. -/
theorem compareSort_transCmp : ∀ orders : List (Bool × Collation), Std.TransCmp (compareSort orders)
  | [] => { eq_swap := by simp [compareSort], isLE_trans := by simp [compareSort] }
  | (descending, collation) :: orders => by
    have := compareTerm_transCmp descending collation
    have := compareSort_transCmp orders
    have := transCmp_on (cmp := compareTerm descending collation) (fun values : List Value => values.headD .null)
    have := transCmp_on (cmp := compareSort orders) (fun values : List Value => values.tail)
    have equal : compareSort ((descending, collation) :: orders) = compareLex
        (fun a b => compareTerm descending collation (a.headD .null) (b.headD .null))
        (fun a b => compareSort orders a.tail b.tail) := by
      funext a b; simp [compareSort, compareLex]
    rw [equal]; exact inferInstance

/-- For every relation, item and list, {name}`insertStable` gives a permutation of the
item followed by the list. Proof sketch: induction over the list; when the item goes
after the head, the result is the head followed by a permutation of the item and the
tail, which one swap turns into the item, the head and the tail. -/
theorem insertStable_perm (le : α → α → Bool) (item : α) :
    ∀ items : List α, (insertStable le item items).Perm (item :: items)
  | [] => .refl _
  | head :: tail => by
    unfold insertStable
    split
    · exact ((insertStable_perm le item tail).cons head).trans (.swap item head tail)
    · exact .refl _

/-- For every relation, starting list and list of items, inserting the items one by
one with {name}`insertStable` gives a permutation of the starting list followed by
the items. Proof sketch: induction over the items, for every starting list; each
insertion is a permutation of the item in front of the starting list
({name}`insertStable_perm`), and moving the item from the front to the middle is a
permutation too. -/
theorem foldl_insertStable_perm (le : α → α → Bool) :
    ∀ (items start : List α), (items.foldl (fun sorted item => insertStable le item sorted) start).Perm (start ++ items)
  | [], start => by simp
  | item :: items, start => by
    simp only [List.foldl_cons]
    refine (foldl_insertStable_perm le items _).trans ?_
    exact ((insertStable_perm le item start).append_right items).trans List.perm_middle.symm

/-- For every relation and list, {name}`stableSort` gives a permutation of the list:
the sort neither adds, drops nor repeats an item. Proof sketch: the sort inserts the
items into an empty list, so {name}`foldl_insertStable_perm` applies with an empty
starting list. -/
theorem stableSort_perm (le : α → α → Bool) (items : List α) : (stableSort le items).Perm items := by
  simpa [stableSort] using foldl_insertStable_perm le items []

/-- For every table, the rows of a full scan ({name}`Belay.Sqlite.Table.scanRows`) are a
permutation of its rows, in rowid or in key order. Proof sketch: both branches of the scan
are a {name}`stableSort` of the rows, which {name}`stableSort_perm` permutes. -/
theorem _root_.Belay.Sqlite.Table.scanRows_perm (table : Table) : table.scanRows.Perm table.rows := by
  unfold Table.scanRows
  split <;> exact stableSort_perm _ _

/-- For every relation {lit}`le` that is transitive and total (for all {lit}`a` and
{lit}`b`, {lit}`le a b` or {lit}`le b a`), every item and every list that is in order
by {lit}`le`: the result of {name}`insertStable` is in order by {lit}`le`. Proof
sketch: induction over the list. When the item goes after the head, the head is at
most the item and every later item; when it goes before the head, totality puts the
item at most the head, and transitivity at most every later item. -/
theorem insertStable_sorted (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (item : α) :
    ∀ items : List α, items.Pairwise (le · ·) → (insertStable le item items).Pairwise (le · ·)
  | [], _ => by simp [insertStable]
  | head :: tail, sorted => by
    rw [List.pairwise_cons] at sorted
    unfold insertStable
    split
    · rename_i before
      refine List.pairwise_cons.2 ⟨fun x member => ?_, insertStable_sorted le trans total item tail sorted.2⟩
      rcases List.mem_cons.1 ((insertStable_perm le item tail).mem_iff.1 member) with equal | later
      · exact equal ▸ before
      · exact sorted.1 x later
    · rename_i after
      have first : le item head := by simpa [after] using total head item
      refine List.pairwise_cons.2 ⟨fun x member => ?_, List.pairwise_cons.2 sorted⟩
      rcases List.mem_cons.1 member with equal | later
      · exact equal ▸ first
      · exact trans _ _ _ first (sorted.1 x later)

/-- For every transitive and total relation {lit}`le` and every list, the result of
{name}`stableSort` is in order by {lit}`le`: each item is at most every later item.
Proof sketch: each insertion keeps the order ({name}`insertStable_sorted`). -/
theorem stableSort_sorted (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (items : List α) : (stableSort le items).Pairwise (le · ·) := by
  suffices ∀ (items start : List α), start.Pairwise (le · ·) →
      (items.foldl (fun sorted item => insertStable le item sorted) start).Pairwise (le · ·) from
    this items [] .nil
  intro items
  induction items with
  | nil => exact fun _ sorted => sorted
  | cons item items ih => exact fun start sorted => ih _ (insertStable_sorted le trans total item start sorted)

/-- For every list of directions and records, the sorted records are a permutation
of the records: the sort neither adds, drops nor repeats a record. -/
theorem sort_perm (directions : List (Bool × Collation)) (items : List Record) :
    (stableSort (fun a b => (compareSort directions a.2 b.2).isLE) items).Perm items :=
  stableSort_perm _ _

/-- For every list of directions and records, the sorted records are in order:
each record compares as less than or equal to every later record by the
{lit}`ORDER BY` terms. The proof uses {name}`stableSort_sorted` with the
transitivity and totality of {name}`compareSort`. -/
theorem sort_sorted (directions : List (Bool × Collation)) (items : List Record) :
    (stableSort (fun a b => (compareSort directions a.2 b.2).isLE) items).Pairwise
      fun a b => (compareSort directions a.2 b.2).isLE := by
  have := compareSort_transCmp directions
  apply stableSort_sorted
  · intro a b c first second
    exact Std.TransCmp.isLE_trans first second
  · intro a b
    rw [Std.OrientedCmp.eq_swap (cmp := compareSort directions) (a := b.2)]
    cases compareSort directions a.2 b.2 <;> rfl

/-- For every evaluation context, query and list of rows, a row is in {name}`filtered`
exactly when it is in the list and the {lit}`WHERE` condition, if any, is true for it in
the context. -/
theorem mem_filtered (context : EvalContext) (query : Query) (rows : List (List Value)) (row : List Value) :
    row ∈ filtered context query rows ↔
      row ∈ rows ∧ query.filter.all (fun condition => truthy (condition.eval context row)) = true := by
  simp [filtered]

/-- For every list of records, offset and limit, the window keeps the records after
the first {lit}`offset`, at most {lit}`limit` of them: its length is the smaller of
the limit and the number of records after the offset. -/
theorem window_length (items : List Record) (offset limit : Nat) :
    ((items.drop offset).take limit).length = min limit (items.length - offset) := by
  simp

/-- For every evaluation context and group of rows, {lit}`COUNT(*)` is the number of rows
in the group. -/
theorem countRows_eval (context : EvalContext) (group : List (List Value)) :
    Aggregate.countRows.eval context group = .integer group.length := rfl

end Belay.Sqlite.Resolved
