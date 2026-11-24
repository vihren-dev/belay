import Belay.Sqlite.Programs.Claims.ReadStepRule
import Belay.Sqlite.Programs.Automation.SqlRunShape

set_option doc.verso true

/-! The rules that {lit}`sql_run` applies (ADR 0017, S6): for each kind of program step the public rule
and how the tactic treats each premise of the rule. The rules are theorems with their own proofs; this
module only chooses among them, so a wrong choice makes the tactic fail and cannot make it accept a false
goal. -/

namespace Belay.Sqlite.Run
open Lean Elab Tactic

/-- The most rules that one run of {lit}`sql_run` applies along one path of the program. The limit stops a
program that unfolds without end; a real program is far below it. -/
def traversalFuel : Nat := 400

/-- Only an open SELECT syntax check blocks traversal of its continuation. -/
def blockingPremises : List Name := [`isSelect]

/-- The premises used by the syntax rules for SELECT, query and single. -/
def premiseNames : List Name := [`modeled, `reached, `isSelect]

end Belay.Sqlite.Run
