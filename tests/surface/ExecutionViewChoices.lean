import ExecutionViewComparisons

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionViewComparisonExamples
open Belay.Sqlite Belay.Sqlite.Model

/-- Raw and concrete outputs select opposite returned values in the two programs. -/
def selectedValue (swapped : Bool) (output : Output) : Nat :=
  if output == .rows [[1]] then (if swapped then 1 else 2) else (if swapped then 2 else 1)

/-- Both programs permit returned values 1 and 2, but their actual raw choices differ. -/
def choices (swapped : Bool) : Sql Nat :=
  let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values fun output => .pure (selectedValue swapped output)

/-- The ambiguous query's raw output lists both permitted concrete rows.
Proof sketch: reduce the installed interpreter on the two-row fixture. -/
theorem choices_step :
    let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
    runScriptStep runContext initial.clock initial.index initial.connection statement values =
      .continued (.oneOf [[[1]], [[2]]]) initial.connection [] := by rfl

/-- Every raw/concrete branch of either program has one of the two quiet observations.
Proof sketch: invert the step and pure continuation, then enumerate its three choices. -/
theorem choices_observation (swapped : Bool) {result : SqlRun Nat}
    (branch : (choices swapped).Branch initial.clock initial.index initial.connection result) :
    (Sql.View.quiet (choices swapped)).observation result = (some 1, []) ∨
      (Sql.View.quiet (choices swapped)).observation result = (some 2, []) := by
  obtain ⟨selected, later, choice, tail, rfl⟩ := (Sql.branch_continued_iff choices_step result).mp branch
  have later_eq := (Sql.branch_pure_iff (selectedValue swapped selected) _ _ _ later).mp tail
  subst later
  have alternatives : selected = .oneOf [[[1]], [[2]]] ∨ selected = .rows [[1]] ∨ selected = .rows [[2]] := by
    simpa [OutputChoice] using choice
  rcases alternatives with rfl | rfl | rfl <;> cases swapped <;>
    first | exact Or.inl rfl | exact Or.inr rfl

/-- Each quiet returned value has a branch in either program, including a concrete
choice where needed. Proof sketch: choose raw or the first concrete row, then return. -/
theorem choices_member (swapped : Bool) (value : Nat) (member : value = 1 ∨ value = 2) :
    ∃ result, (choices swapped).Branch initial.clock initial.index initial.connection result ∧
      (Sql.View.quiet (choices swapped)).observation result = (some value, []) := by
  let selected := if (swapped && value == 1) || (!swapped && value == 2)
    then Output.rows [[1]] else .oneOf [[[1]], [[2]]]
  have choice : OutputChoice (.oneOf [[[1]], [[2]]]) selected := by
    dsimp [selected]
    split
    · exact OutputChoice.rows (by simp)
    · exact .actual _
  refine ⟨_, Sql.Branch.continued_own choices_step choice (Sql.Branch.pure (selectedValue swapped selected) _ _ _), ?_⟩
  rcases member with rfl | rfl <;> cases swapped <;> rfl

/-- Both programs have exactly the same weak projected branch-observation set.
Proof sketch: classify each branch's value and choose a matching branch on the other side. -/
theorem equal_branch_observations : ∀ observation,
    (∃ result, (choices false).Branch initial.clock initial.index initial.connection result ∧
      (Sql.View.quiet (choices false)).observation result = observation) ↔
    (∃ result, (choices true).Branch initial.clock initial.index initial.connection result ∧
      (Sql.View.quiet (choices true)).observation result = observation) := by
  intro observation
  constructor
  · rintro ⟨result, branch, seen⟩
    rcases choices_observation false branch with first | second
    · obtain ⟨other, matched, equal⟩ := choices_member true 1 (Or.inl rfl)
      exact ⟨other, matched, equal.trans (first.symm.trans seen)⟩
    · obtain ⟨other, matched, equal⟩ := choices_member true 2 (Or.inr rfl)
      exact ⟨other, matched, equal.trans (second.symm.trans seen)⟩
  · rintro ⟨result, branch, seen⟩
    rcases choices_observation true branch with first | second
    · obtain ⟨other, matched, equal⟩ := choices_member false 1 (Or.inl rfl)
      exact ⟨other, matched, equal.trans (first.symm.trans seen)⟩
    · obtain ⟨other, matched, equal⟩ := choices_member false 2 (Or.inr rfl)
      exact ⟨other, matched, equal.trans (second.symm.trans seen)⟩

/-- Equal branch sets alone do not establish projected comparison: actual raw runs
return different values. Proof sketch: the actual-equality field would equate 1 and 2. -/
theorem actual_agreement_is_required :
    ¬ (Sql.View.quiet (choices false)).ObservationEquivAt (Sql.View.quiet (choices true)) initial := by
  intro same
  have value := congrArg Prod.fst same.actual
  have impossible : (some 1 : Option Nat) = some 2 := value
  cases impossible

#print axioms choices_step
#print axioms choices_observation
#print axioms choices_member
#print axioms equal_branch_observations
#print axioms actual_agreement_is_required
end ExecutionViewComparisonExamples
