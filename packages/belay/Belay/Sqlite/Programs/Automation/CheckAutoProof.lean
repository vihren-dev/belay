import Belay.Sqlite.Programs.Automation.AutoSearch
import Belay.Sqlite.Programs.Claims.AssertionTerms

set_option doc.verso true

namespace Belay.Sqlite.Check
open Lean Meta Elab Term Tactic

/-- The hints of the default search: the resolution of a statement and the model coverage of a statement hold
by evaluation on a concrete database. A claim that needs other facts has no default proof, and the user proves
it with the explicit tactics and the hints that it needs. -/
def defaultSearchHints : TermElabM (Array (TSyntax `term)) :=
  return #[← `(rfl), ← `(⟨_, _, _, rfl⟩)]

/-- Definitions from these module roots give library propositions their structure.
Keep their heads visible so the query and program routes can recognize them. -/
private def libraryModuleRoots : List Name := [`Init, `Lean, `Std, `Belay]

/-- The tactic that opens a claim to the form of the search: a fresh triple with the assertion {lit}`ifOk`
becomes its check of the program at the initial context. First unfold names of claims from the user's
modules so that the binders are visible. Every variable is introduced, and an equation that a
premise gives for a variable replaces the variable. -/
def openingTactic (proposition : Expr) : TermElabM (TSyntax `tactic) := do
  let environment ← getEnv
  let mut claim := proposition.consumeMData
  let mut names := #[]
  while let some name := claim.getAppFn.constName? do
    let some (.defnInfo _) := environment.find? name | break
    if (environment.getModuleIdxFor? name).any fun index =>
        libraryModuleRoots.contains (environment.header.moduleNames[index.toNat]!).getRoot then break
    let some body ← unfoldDefinition? claim | break
    names := names.push (mkIdent name)
    claim := body.consumeMData
  let openGoal ← `(tactic| ((first | refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_ | skip); intros; try subst_vars))
  if names.isEmpty then return openGoal
  return ← `(tactic| (unfold $names:ident*; $openGoal:tactic))

end Belay.Sqlite.Check
