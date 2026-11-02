import ProbeModel

/-! Exercise diagnostics, proof checking and compiled dependency export. -/

namespace Probe

/-- The classification of zero is zero; reuse the subject's named lemma. -/
theorem fromLemma : ProbeModel.classify 0 = 0 := ProbeModel.zero

/-- The classification of two is one; ask the kernel to decide this concrete case. -/
theorem concreteCase : ProbeModel.classify 2 = 1 := by decide +kernel

end Probe

#print axioms Probe.fromLemma
#print axioms Probe.concreteCase
#eval ProbeModel.classify 2
