import Belay.Sqlite.Programs.Claims.SendStatementsInvariant
import Belay.Sqlite.Model.Programs.Scripts.SchemaPath

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every successfully resolved script and every branch of its sent statements
from a valid connection with the starting resolution state, if the branch returns
and all its outputs succeed, its ending resolution state is the resolver's final
state. The rows, counters and order of query results can differ between branches.
Proof sketch: use the prefix state as the indexed branch invariant. Resolution at
each prefix gives the next state, and every successful execution reaches it. -/
theorem sendStatements_branch_resolveState {statements : List (Syntax.Statement × List Value)}
    {initial final : ResolveState} {resolved : List Resolved.Statement} {clock : Option Clock} {index : Nat}
    {c : Connection} {result : SqlRun (List Output)}
    (checked : resolveFrom runContext 0 initial (statements.map Prod.fst) = .ok (resolved, final))
    (start : c.resolveState = initial) (valid : c.state.Holds (Database.Valid Profile.pinned))
    (branch : (sendStatements statements).Branch clock index c result)
    (returned : result.value.isSome = true) (ok : result.outputs.allOk = true) :
    result.connection.resolveState = final := by
  have reached := sendStatements_branch_invariant statements
    (fun n connection => connection.resolveState = initial.atPrefix resolved n)
    clock index c result branch returned ok valid start (by
      intro n bound i conn _ same output next others step execution member good
      have atStmt : (statements.map Prod.fst)[n]? = some statements[n].1 := by simp [bound]
      obtain ⟨r, _, resolution⟩ := resolveFrom_atPrefix checked atStmt
      rw [← same] at resolution
      exact runScriptStep_resolveState resolution step member good)
  obtain ⟨ended, length⟩ := resolveFrom_final checked
  rw [List.length_map] at length
  simpa [ResolveState.atPrefix, ← length, ended] using reached

end Belay.Sqlite
