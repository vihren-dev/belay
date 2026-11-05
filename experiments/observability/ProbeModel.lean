/-! A small executable and proof subject for the observability experiments. -/

namespace ProbeModel

/-- Return zero for zero and one for every positive natural number. -/
def classify (n : Nat) : Nat := if n == 0 then 0 else 1

/-- The model classifies zero as zero, by reducing its definition. -/
theorem zero : classify 0 = 0 := by rfl

end ProbeModel
