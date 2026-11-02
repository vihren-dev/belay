import Belay.Sqlite.ProofCost

/-! Exercise the existing optional collector without adding another Lean hook. -/

set_option belay.proofCosts true

/-- Forty natural numbers occur in the range from zero through thirty-nine. -/
theorem counted : (List.range 40).length = 40 := by decide +kernel
