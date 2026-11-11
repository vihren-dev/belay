import Belay.Sqlite.Queries.Automation.SqlSelectLeaf
import Belay.Sqlite.Queries.Automation.SqlSelectRules
import Lean.Meta.Tactic.Subst

set_option doc.verso true

namespace Belay.Sqlite.Select
open Lean Meta Elab Tactic

/-- For every list of length {lit}`n + 1`, the list is a first element and a rest of length {lit}`n`. -/
theorem cons_of_length_succ {α : Type} {list : List α} {n : Nat} (length : list.length = n + 1) :
    ∃ head tail, list = head :: tail ∧ tail.length = n := by
  cases list with
  | nil => simp at length
  | cons head tail => exact ⟨head, tail, rfl, by simpa using length⟩

/-- The rules to try on a goal or a fact of the phases: the hints in the given order, then the
registered rules. -/
def candidates (hints : Hints) (phases : List SelectPhase) : TacticM (Array (Sum Name (TSyntax `term))) := do
  return hints.map .inr ++ (← registeredSelectRules phases).map (.inl ·.2)

/-- The key of a rule in the record of applied steps: its name, or the text of a hint. -/
def ruleKey : Sum Name (TSyntax `term) → String
  | .inl name => toString name
  | .inr hint => toString hint.raw.prettyPrint

/-- Report where the procedure stopped and why; the goal stays open. -/
def explain (goal : MVarId) (phase : String) (reason : MessageData) : TacticM Unit :=
  logWarning m!"sql_select stopped in the {phase} phase: {reason} The goal stays open:{indentD (MessageData.ofGoal goal)}"

/-- The number of rule applications in one run of {lit}`sql_select`: the
rules applied backward to the goal and forward to its hypotheses, together. Cyclic rules and hints stop
at this limit. -/
def selectFuel : Nat := 64

/-- The explanation of a goal on which the procedure used all its rule applications ({name}`selectFuel`).
The limit is no evidence that the goal is false. -/
def exhausted : MessageData :=
  m!"the procedure used its limit of {selectFuel} rule applications. Rules or hints that make new goals or \
    facts without end use this limit. This does not show that the goal is false. Pass fewer hints, or \
    prove the goal in steps."

/-- The procedure of {lit}`sql_select` with the given hints, as a sequence of steps of
{lit}`sql_select` on the main goal. -/
syntax (name := sqlSelect) "sql_select" (" [" term,* "]")? : tactic

end Belay.Sqlite.Select
