import Belay.Sqlite.AutoSearch
import Belay.Sqlite.AssertionTerms
import Belay.Sqlite.CheckProof

set_option doc.verso true

/-! The default proof attempt of the SQL checker: the short closing tactics of {name}`Belay.Sqlite.Check.tryProof`, then the
search of {lit}`sql_auto` on the check of a program. The search needs the checks of a program in the form
that {lit}`sql_run` reads, so the attempt first opens a fresh triple to that form. The result is a script of
explicit steps: the checker elaborates it again without a search, and the kernel checks its proof against the
original claim. -/

namespace Belay.Sqlite.Check
open Lean Meta Elab Term Tactic Belay.Sqlite.Run

/-- The hints of the default search: the resolution of a statement and the model coverage of a statement hold
by evaluation on a concrete database. A claim that needs other facts has no default proof, and the user proves
it with the explicit tactics and the hints that it needs. -/
def defaultSearchHints : TermElabM (Array (TSyntax `term)) :=
  return #[← `(rfl), ← `(⟨_, _, _, rfl⟩)]

/-- The tactic that opens a claim to the form of the search: a fresh triple with the assertion {lit}`ifOk`
becomes its check of the program at the initial context, every variable is introduced, and an equation that a
premise gives for a variable replaces the variable. -/
def openingTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| ((first | refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_ | skip); intros; try subst_vars))

/-- Search for a proof of a claim that opens to the check of a program, with the routes of {lit}`sql_auto`,
using at most a third of the budget that is left. The script of the result holds the opening and the explicit steps of the winning route, so it
proves the claim again without a search. None when the claim has no such proof. -/
def searchedProof (proposition : Expr) : TermElabM (Option Proven) := do
  let opening ← openingTactic
  let hints ← defaultSearchHints
  let share := (← remainingUnits) / 3
  let found ← withinBudget share <| attempt do
    let goal ← mkFreshExprMVar proposition
    let [opened] ← runStrict goal.mvarId! opening | throwError "the claim has no single goal after the opening"
    -- The search is for the check of a program. Other claims have no route, and a search would use the budget.
    unless (← checkProgram? (← opened.getType)).isSome do throwError "the opened claim is no check of a program"
    let .ok found ← search hints opened | throwError "no route closes the goal"
    let steps := found.steps
    let script ← `(tactic| ($opening:tactic; $[$steps:tactic];*))
    return (script, ← instantiateMVars goal)
  let some (some (script, proof)) := found | return none
  return some { proof, tactic := printableScript script }

/-- The default proof attempt: the closing tactics first, because they are cheap, then the search. -/
def defaultProof (proposition : Expr) : TermElabM (Option Proven) := do
  if let some proven ← tryProof proposition then return some proven
  searchedProof proposition

end Belay.Sqlite.Check
