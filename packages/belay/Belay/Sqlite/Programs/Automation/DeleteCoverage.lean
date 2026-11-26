import Belay.Sqlite.Programs.Automation.DeleteCoverageRows
import Belay.Sqlite.Programs.Reasoning.ExecutionContext

set_option doc.verso true

/-! After the send rule exposes a plain DELETE step, this scoped tactic discharges its coverage
check using the step equation, the target table, and facts about the filter. -/

namespace Belay.Sqlite.Run.DeleteCoverage
open Belay.Sqlite.Model
open PlainDeleteCoverage
open Lean Meta Elab Tactic

attribute [delete_row_fact] absComparison jsonComparison inProjection

/-- Close the coverage goal for a plain DELETE with its step equation and target table lookup.
Use after {lit}`sql_run` in the modeled case. Clock and counter facts come from the local context.
Facts tagged {lit}`delete_row_fact` can prove safety for rows that satisfy the supplied premises. -/
scoped elab "cover_delete " rule:term ", " present:term : tactic => do
  evalTactic (← `(tactic|
    (rw [$rule:term]
     try simp only [ExecutionContext.initial, Database.Raw.connection]
     first | rw [timed_without_read (by rfl)] | rw [timed_with_clock (by rfl) (by assumption)]
     simp only
     first | rw [no_counters _ _ (by rfl)] | rw [changes_known (by rfl) (by assumption)]
     simp only [$present:term])))
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some guard := target.find? (fun e => e.isAppOfArity ``deleteJsonReady 4)
      | throwError "Expected the filter check for a plain DELETE. Check the step equation and target table."
    let test ← Term.exprToSyntax guard
    evalTactic (← `(tactic|
      (have ready : $test = true := by
         apply ready_of_rows
         intro row member
         first | rfl | solve_by_elim (maxDepth := 4) using $(Lean.mkIdent `delete_row_fact):ident
       simp only [ready]
       rfl)))

end Belay.Sqlite.Run.DeleteCoverage
