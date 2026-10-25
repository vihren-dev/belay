import Belay.Sqlite.CheckInputs
import Belay.Sqlite.CheckDisplay

set_option doc.verso true

/-! The explicit SQL checking command elaborates a proposition in its native local context
and delegates search, certification and replay to the shared checking operation. -/

namespace Belay.Sqlite
open Lean Elab Command Meta

/-- Check a proposition with kernel-certified proof search or a replayable counterexample.
For example, {lit}`#sql_check ∀ db : Database, Empty (sql "SELECT 1") db` reports false.
Optional {lit}`with (schema := database)`, repeated {lit}`(db := database)`,
{lit}`(env := environment)` and {lit}`(input name := value)` guide the same checker.
The {lit}`sql.checkBudget` and {lit}`sql.checkCandidates` options bound the search;
an unknown result proves nothing. The command adds no theorem. -/
syntax (name := sqlCheckCommand) "#sql_check " term
  (" with " sqlCheckInput+)? : command

/-- Elaborate the original proposition in the command's local context and display only the
shared checker's result. Normal Lean cancellation remains attached to this command. -/
@[command_elab sqlCheckCommand]
def elabSqlCheckCommand : CommandElab := fun stx => do
  let `(command| #sql_check $proposition $[with $inputs:sqlCheckInput*]?) := stx
    | throwUnsupportedSyntax
  let message ← runTermElabM fun _ => Term.withoutErrToSorry do
    let proposition ← Term.elabTerm proposition (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    let proposition ← instantiateMVars proposition
    Check.describe (← Check.configuredCheck proposition (inputs.getD #[]))
  logInfo message

end Belay.Sqlite
