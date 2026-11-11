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

/-- The tactic that opens a claim to the form of the search: a fresh triple with the assertion {lit}`ifOk`
becomes its check of the program at the initial context, every variable is introduced, and an equation that a
premise gives for a variable replaces the variable. -/
def openingTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| ((first | refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_ | skip); intros; try subst_vars))

end Belay.Sqlite.Check
