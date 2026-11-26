import Belay.Sqlite.Programs.Automation.DeleteCoverageRows
import Belay.Sqlite.Programs.Reasoning.ExecutionContext

set_option doc.verso true

namespace Belay.Sqlite.Run.DeleteCoverage
open Belay.Sqlite.Model
open Lean Meta Elab Tactic

attribute [delete_row_fact] absComparison jsonComparison inProjection

/-- A DELETE without RETURNING passes the filter check if the filter is safe on the empty
row and on every stored row. -/
private theorem ready_of_rows {ctx : Resolved.EvalContext} {table : Table} {filter : Option Resolved.Expr}
    (safe : ∀ row ∈ [] :: table.rows.map Row.values, filter.toList.any (·.mayFailOn ctx row) = false) :
    deleteJsonReady ctx table filter [] = true := by
  unfold deleteJsonReady Resolved.anyMayFail
  rw [List.any_eq_false.mpr (fun row mem => by rw [safe row mem]; decide)]
  rfl

/-- A statement without counter reads has no unknown counter. -/
private theorem no_counters (s : Resolved.Statement) (c : Counters) (empty : s.counterReads = []) :
    c.firstUnknown s.counterReads = none := by rw [empty]; rfl

/-- A statement without clock reads gets the constant clock value zero. -/
private theorem timed_without_read {s : Resolved.Statement} (h : s.readsClock = false) :
    statementClock clock index s = some 0 := by simp [statementClock, h]
/-- A clock-reading statement gets the supplied clock value at its statement index. -/
private theorem timed_with_clock {s : Resolved.Statement} (h : s.readsClock = true)
    (known : clock = some f) : statementClock clock index s = some (f index) := by
  simp [statementClock, h, known]
/-- A statement that reads only changes() has its counter when the change count is known. -/
private theorem changes_known {s : Resolved.Statement} {c : Counters}
    (reads : s.counterReads = [.changes]) (known : c.changes = some n) :
    c.firstUnknown s.counterReads = none := by simp [reads, Counters.firstUnknown, Counters.read, known]

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
