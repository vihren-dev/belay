import Belay.Sqlite.Tooling.ProofCost.ProofCostRun

/-! Call the existing report function with one explicitly selected fixture module. -/

/-- Print the existing JSON report of the already compiled fixture. -/
def main : IO UInt32 :=
  Belay.Sqlite.runCosts #[("fixture", #[{
    name := "CostFixture"
    olean := ".lake/build/lib/lean/CostFixture.olean"
    source := "CostFixture.lean"
  }])] { json := true }
