import Belay.Sqlite.Model.Programs.Scripts.SchemaPath
import Belay.Sqlite.Model.Programs.Scripts.SchemaSuccess

set_option doc.verso true

/-! Locate the positions at which a migration needs a success proof from its caller. -/

namespace Belay.Sqlite.Model

/-- The positions in the resolved script whose success the schema check cannot certify.
An empty list certifies every step. Each step uses its own input resolution state. -/
def ResolveState.uncheckedSteps (initial : ResolveState) : List Resolved.Statement → List Nat
  | [] => []
  | first :: rest =>
    let later := ((initial.after first).uncheckedSteps rest).map (· + 1)
    if first.succeedsBySchema initial then later else 0 :: later

/-- If the schema check fails at a position containing a resolved statement, that
position occurs in {name}`ResolveState.uncheckedSteps`. Proof sketch: the first
position uses the initial state. The remaining positions use the successor state. -/
theorem ResolveState.mem_uncheckedSteps {initial : ResolveState} {path : List Resolved.Statement}
    {r : Resolved.Statement} {n : Nat} (atR : path[n]? = some r)
    (failed : r.succeedsBySchema (initial.atPrefix path n) = false) : n ∈ initial.uncheckedSteps path := by
  induction path generalizing n initial with
  | nil => simp at atR
  | cons first rest ih =>
    cases n with
    | zero => cases atR; simp [uncheckedSteps, show r.succeedsBySchema initial = false from failed]
    | succ n =>
      have earlier := ih (initial := initial.after first) (n := n) (by simpa using atR) failed
      unfold uncheckedSteps
      split <;> simp [earlier]

end Belay.Sqlite.Model
