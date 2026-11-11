import Belay.Sqlite.Model.Queries.Evaluation.QueryOutputFacts

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A fault that is not {lit}`may` is not {lit}`must` exactly when it is {lit}`none`: the model
describes a query only when its faults are none or {lit}`must`. Proof sketch: case analysis on the
three faults; the case {lit}`may` is excluded by the hypothesis. -/
theorem Resolved.Fault.ne_must_iff_none (fault : Resolved.Fault) (notMay : fault ≠ .may) :
    fault ≠ .must ↔ fault = .none := by
  cases fault <;> simp_all

end Belay.Sqlite.Model
