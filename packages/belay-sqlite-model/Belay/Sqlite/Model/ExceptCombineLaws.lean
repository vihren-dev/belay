import Belay.Sqlite.Model.CompoundRows
import Belay.Sqlite.Model.IntegerCompareLaws

set_option doc.verso true

/-! Laws of the rows of {lit}`EXCEPT` (ADR 0017, S6). When every row of the left operand is a row of the right
operand, {lit}`EXCEPT` has no row. The purge claim relies on this law: the rows of the initial database that the
purge keeps are also rows of the reached database, so the difference is empty. -/

namespace Belay.Sqlite.Model

/-- For every collation and value, the value compares equal to itself. Proof sketch: a collation compares by an
oriented comparison, which swaps its result when the operands swap; the result for equal operands is its own swap, so
it is {lit}`eq`. -/
theorem Collation.compare_self (collation : Collation) (value : Value) : collation.compare value value = .eq := by
  have swap := Std.OrientedCmp.eq_swap (cmp := collation.compare) (a := value) (b := value)
  cases h : collation.compare value value <;> simp [h] at swap ⊢

/-- For every collations and row, the row is the same output as itself ({name}`Resolved.sameOutput`). Proof sketch:
the lengths agree, and each pair of cells is a cell with itself. -/
theorem Resolved.sameOutput_self (collations : List Collation) (row : List Value) :
    Resolved.sameOutput collations row row = true := by
  have zipSelf : ∀ (cells : List Value) (a b : Value), (a, b) ∈ cells.zip cells → a = b := by
    intro cells
    induction cells with
    | nil => simp
    | cons head tail ih =>
      intro a b member
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | member
      · rfl
      · exact ih a b member
  unfold Resolved.sameOutput
  simp only [Bool.and_eq_true, beq_self_eq_true, List.all_eq_true, true_and]
  intro entry member
  obtain ⟨collation, a, b⟩ := entry
  have same := zipSelf row a b (List.of_mem_zip member).2
  subst same
  simp [Collation.compare_self]

/-- For every collations and rows, a row that {name}`Resolved.distinctRows` keeps is one of the rows. Proof sketch:
the fold appends only the rows that it reads. -/
theorem Resolved.mem_of_mem_distinctRows (collations : List Collation) (rows : List (List Value))
    (row : List Value) (kept : row ∈ Resolved.distinctRows collations rows) : row ∈ rows := by
  have step : ∀ (items start : List (List Value)), (∀ x ∈ start, x ∈ rows) → (∀ x ∈ items, x ∈ rows) →
      ∀ x ∈ items.foldl (fun kept row => if kept.any (Resolved.sameOutput collations · row) then kept else kept ++ [row])
        start, x ∈ rows := by
    intro items
    induction items with
    | nil => intro start hs _ x hx; exact hs x hx
    | cons head tail ih =>
      intro start hs hi x hx
      refine ih _ ?_ (fun y hy => hi y (List.mem_cons_of_mem _ hy)) x hx
      intro y hy
      by_cases seen : (start.any (Resolved.sameOutput collations · head)) = true
      · change y ∈ (if (start.any (Resolved.sameOutput collations · head)) = true then start else start ++ [head]) at hy
        simp only [seen, ↓reduceIte] at hy
        exact hs y hy
      · change y ∈ (if (start.any (Resolved.sameOutput collations · head)) = true then start else start ++ [head]) at hy
        simp only [seen] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hs y hy
        · rw [List.mem_singleton.mp hy]
          exact hi head (List.mem_cons_self ..)
  exact step rows [] (by simp) (fun _ h => h) row kept

/-- For every collations and rows such that every left row is a right row, {lit}`EXCEPT` of them has no row. In plain
words: removing the rows that equal a right row leaves nothing when each left row occurs on the right. Proof sketch:
a kept row is a left row ({name}`Resolved.mem_of_mem_distinctRows`), so it is a right row and equals itself
({name}`Resolved.sameOutput_self`), and the operator removes it. -/
theorem CompoundOperator.except_combine_eq_nil (collations : List Collation) (left right : List (List Value))
    (subset : ∀ row ∈ left, row ∈ right) : CompoundOperator.except.combine collations left right = [] := by
  unfold CompoundOperator.combine
  simp only [List.filter_eq_nil_iff, Bool.not_eq_true', Bool.not_eq_false, List.any_eq_true]
  intro row member
  exact ⟨row, subset row (Resolved.mem_of_mem_distinctRows collations left row member), Resolved.sameOutput_self collations row⟩

end Belay.Sqlite.Model
