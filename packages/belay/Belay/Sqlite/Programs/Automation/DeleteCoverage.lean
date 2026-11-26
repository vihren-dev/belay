import Belay.Sqlite.Programs.Automation.DeleteCoverageRows
import Belay.Sqlite.Programs.Reasoning.ExecutionContext

set_option doc.verso true

/-! After the send rule exposes a plain DELETE step, this scoped tactic discharges its coverage
check using the step equation, the target table, and facts about the filter. -/

namespace Belay.Sqlite.Run.DeleteCoverage
open Belay.Sqlite.Model
open PlainDeleteCoverage Resolved.CallSafety
open Lean Meta Elab Tactic

/-- Let row proof search reuse an existing successful text extraction as path evidence. -/
private theorem pathsOfExtraction {v paths} (ok : Returns (Json.extract v paths)) : ExtractInputs v paths :=
  (extractInputs_iff v paths).mpr ok

-- Default row facts for table projections and function calls. Callers can add local facts.
attribute [delete_row_fact] inProjection scalarSucceeds jsonSucceeds pathsOfExtraction

/-- Decompose a filter into argument and call checks. Apply user facts at each call. -/
private def solveDeleteCalls : TacticM (TSyntax `tactic) := `(tactic|
  (apply filterSafe
   repeat' first
     | assumption
     | exact succeedsOk _
     | rfl
     | exact of_decide_eq_true rfl
     | apply compareFault
     | apply consFault
     | apply iifFault
     | apply scalarFault
     | apply jsonFault
     | apply dateFault
     | solve_by_elim (maxDepth := 5) [True.intro] using $(Lean.mkIdent `delete_row_fact):ident
   done))

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
    let calls ← solveDeleteCalls
    evalTactic (← `(tactic|
      (have ready : $test = true := by
         apply ready_of_rows
         intro row member
         first
         | rfl
         | solve_by_elim (maxDepth := 4) using $(Lean.mkIdent `delete_row_fact):ident
         | $calls:tactic
         | rcases List.mem_cons.mp member with empty | stored
           · subst row
             first | rfl | $calls:tactic
           · obtain ⟨r, mem, eq⟩ := List.mem_map.mp stored
             subst row
             $calls:tactic
       simp only [ready]
       rfl)))

end Belay.Sqlite.Run.DeleteCoverage
