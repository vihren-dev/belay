import Belay

/-! The balance proof's SUM bound must include REAL values retained by INTEGER affinity.
These consumers use the general bound theorem; finite checks exercise mixed inputs and
an overflow immediately beyond a safe bound. -/

open Belay.Sqlite.Model

/-- Every numeric or NULL list with fewer than a million cells and integer cells bounded
by a trillion has a SUM value. Proof sketch: the general product bound fits in 64 bits. -/
theorem ledger_sum_bound (values : List Value)
    (numeric : ∀ value ∈ values, value = .null ∨ (∃ n, value = .integer n) ∨ (∃ r, value = .real r))
    (bounded : ∀ n ∈ integerCells values, -1000000000000 ≤ n ∧ n ≤ 1000000000000)
    (small : values.length < 1000000) : (sumOf values).sumValue.isNone = false := by
  apply sumOf_no_overflow_of_bound values 1000000000000 (by decide) numeric bounded
  omega

/-- The safe-sum theorem accepts NULLs and a REAL between bounded integers. -/
example : (sumOf [.null, .integer 1000000000000, .real 4607182418800017408,
    .integer (-1000000000000)]).sumValue.isNone = false := by
  apply ledger_sum_bound
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  · simp [integerCells]
  · decide

-- A first integer prefix can overflow even when the final exact sum would return to range.
example : (sumOf [.integer 9223372036854775807, .integer 1, .integer (-1)]).sumValue.isNone = true := by
  decide +kernel

-- The safe upper boundary itself is accepted.
example : (sumOf [.integer 9223372036854775807]).sumValue.isNone = false := by
  decide +kernel

#print axioms ledger_sum_bound
#print axioms sumOf_no_overflow_of_bound
