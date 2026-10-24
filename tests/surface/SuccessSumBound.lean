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

/-- Stored INTEGER-affinity inputs satisfying the SQL NOT BETWEEN precondition have a
safe SUM. Proof sketch: the stored range law supplies the same trillion-times-count bound. -/
theorem ledger_sum_from_sql_bounds (values : List Value)
    (stored : ∀ value ∈ values, LiteralData.storedForm .integer value = true)
    (within : ∀ value ∈ values, Resolved.truthy
      ((Comparison.ge.apply (Resolved.numericOperand value) (.integer (-1000000000000))).and
        (Comparison.le.apply (Resolved.numericOperand value) (.integer 1000000000000))).not = false)
    (small : values.length < 1000000) : (sumOf values).sumValue.isNone = false := by
  apply sumOf_no_overflow_of_between values 1000000000000 .binary (by decide)
  · intro value member
    simpa [Resolved.numericOperand_of_stored
      (by decide : Affinity.integer ≠ .text ∧ Affinity.integer ≠ .blob) (stored value member)] using within value member
  · omega

-- A stored nonnumeric TEXT and a BLOB each fail the numeric range, rather than silently
-- acquiring the integer-only premise used in the original guide argument.
example : Resolved.truthy ((Comparison.ge.apply (.text (bytes! "word")) (.integer (-1000000000000))).and
    (Comparison.le.apply (.text (bytes! "word")) (.integer 1000000000000))).not = true := by decide +kernel
example : Resolved.truthy ((Comparison.ge.apply (.blob []) (.integer (-1000000000000))).and
    (Comparison.le.apply (.blob []) (.integer 1000000000000))).not = true := by decide +kernel

#print axioms ledger_sum_from_sql_bounds

/-- Exact INTEGER metadata gives the two affinities for which the SQL range test
preserves integer bounds. No coherence premise about STRICT ANY is hidden. -/
theorem ledger_type_affinity (column : CatalogColumn)
    (reported : pragmaText (column.declaredType.getD "") = pragmaText "INTEGER") :
    column.affinity = .integer ∨ column.affinity = .blob :=
  column.affinity_of_integer_pragma reported

-- Arbitrary catalog values can combine reported INTEGER with STRICT ANY. The
-- bridge keeps the resulting BLOB case; the SUM range argument handles it directly.
example : ({name := name! "cents", declaredType := some "INTEGER", strictType := some .any} : CatalogColumn).affinity = .blob := by decide +kernel
example : ({name := name! "cents", declaredType := some "INTEGER"} : CatalogColumn).affinity = .integer := by
  decide +kernel

#print axioms ledger_type_affinity
#print axioms column_lookup_of_member

-- The named-source bridges also cover callbacks used by preceding sibling subqueries.
#print axioms resolveSources_table
#print axioms resolveSources_tableInfo
