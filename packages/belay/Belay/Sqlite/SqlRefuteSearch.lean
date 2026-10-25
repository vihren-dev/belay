import Belay.Sqlite.SqlRefute
import Belay.Sqlite.CheckInputs

set_option doc.verso true

/-! The searched refutation tactic uses the same bounded operation as the command.
The explicit witness tactic remains a separate primitive for caller-selected evidence. -/

namespace Belay.Sqlite
open Lean Elab Tactic Meta

/-- In a goal {lit}`¬ P`, search for a checked refutation using the same options and inputs
as {lit}`#sql_check`. Optional {lit}`with (db := database)` supplies an ordered candidate;
{lit}`(schema := database)`, {lit}`(env := environment)` and {lit}`(input name := value)`
guide inference. Unknown or a proved original proposition leaves the goal unproved.
The explicit {lit}`sql_refute (db := database)` primitive remains available without search. -/
syntax (name := sqlRefuteSearch) "sql_refute" (" with " sqlCheckInput+)? : tactic

/-- Assign only the shared checker's certified refutation of the original negated goal. -/
@[tactic sqlRefuteSearch]
def elabSqlRefuteSearch : Tactic := fun stx => do
  let `(tactic| sql_refute $[with $inputs:sqlCheckInput*]?) := stx
    | throwUnsupportedSyntax
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some proposition := target.not?
      | throwError "sql_refute expects a goal of the form ¬ P"
    let outcome ← Check.configuredCheck proposition (inputs.getD #[])
    match outcome.result with
    | .refuted _ proof => goal.assign proof
    | .proved _ => throwError "SQL check proved the original proposition; no refutation is available"
    | .unknown => throwError "SQL check found no certified replayable counterexample within the budget; supply a witness or increase the search bounds"
  replaceMainGoal []

end Belay.Sqlite
