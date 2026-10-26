import ExecutionBranches
import Belay.Sqlite.ExecutionSpecifications
import Std.Tactic.Do

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionExamples
open Belay.Sqlite Std.Do

/-- Explicit transaction statements compose with the existing query and single helpers. -/
def commitWrite : Sql (Except Nat (List (List Value)) × Option Value) := do
  let _ ← send (sql r"BEGIN")
  let inserted ← query (sql r"INSERT INTO t VALUES (3, 3) RETURNING x")
  let count ← single (sql r"SELECT count(*) FROM t")
  let _ ← send (sql r"COMMIT")
  pure (inserted, count)

/-- The returned insertion rows contain 3, the returned count is 3, and the final context
records four statements, three stored rows and a closed transaction. -/
abbrev committed (value : Except Nat (List (List Value)) × Option Value) (state : ExecutionContext) : Prop :=
  value = (.ok [[3]], some 3) ∧ state.index = 4 ∧
    state.connection.state.snapshot = none ∧ (state.connection.state.database.rowsAt 0).length = 3

/-- Generic helper specifications let mvcgen verify the real transaction write. -/
theorem helpers_tactic :
    ⦃fun state : ExecutionContext => ⌜state = initial⌝⦄ commitWrite
      ⦃⇓ value state => ⌜committed value state⌝⦄ := by
  unfold commitWrite
  mvcgen
  all_goals subst_vars; rw [← Sql.check_bind]; decide +kernel

/-- Explicit branch rules prove the same transaction fact without mvcgen. -/
theorem helpers_explicit :
    ⦃fun state : ExecutionContext => ⌜state = initial⌝⦄ commitWrite
      ⦃⇓ value state => ⌜committed value state⌝⦄ := by
  intro state entry
  cases entry
  change commitWrite.check committed initial
  unfold commitWrite
  change (Sql.exec .begin [] _).check committed initial
  apply (Sql.check_continued (actual := .done 0) (others := [])
    (connection := ((send (sql r"BEGIN")).runFrom daily.clock 0 initial.connection).connection)
    (by rfl) committed).mpr
  intro found member selected choice
  simp only [Model.RunStep.executions, List.mem_singleton] at member
  subst member
  have observed : selected = .done 0 := choice.elim id False.elim
  cases observed
  decide +kernel

/-- Appending scripts preserves their shared transaction snapshot and actual rollback. -/
theorem helpers_rollback :
    (send ((sql r"BEGIN; INSERT INTO t VALUES (3, 3)") ++ (sql r"ROLLBACK"))).check
      (fun outputs state => outputs.length = 3 ∧ state.index = 3 ∧
        state.connection.state.snapshot = none ∧ (state.connection.state.database.rowsAt 0).length = 2)
      initial := by
  rw [check_send_append]
  decide +kernel

/-- Query returns an SQL error code while single deliberately converts the same error to none. -/
theorem helper_errors :
    (query (sql r"SELECT missing FROM t")).check (fun result _ => result = .error 1) initial ∧
    (single (sql r"SELECT missing FROM t")).check
      (fun result state => result = none ∧ state.outputs.allOk = false) initial := by
  constructor
  · rw [check_query]
    change ∀ found ∈ Model.RunStep.executions (.continued (.error 1) _ []), ∀ selected,
      OutputChoice found.output selected → _
    simp only [Model.RunStep.executions, List.mem_singleton, forall_eq]
    rw [OutputChoice.forall_iff]
    decide +kernel
  · rw [check_single, check_query]
    change ∀ found ∈ Model.RunStep.executions (.continued (.error 1) _ []), ∀ selected,
      OutputChoice found.output selected → _
    simp only [Model.RunStep.executions, List.mem_singleton, forall_eq]
    rw [OutputChoice.forall_iff]
    decide +kernel

/-- COMMIT outside a transaction is a modeled error, so conditional handling stays explicit. -/
theorem commit_error :
    (query (sql r"COMMIT")).check
      (fun value state => value = .error 1 ∧ state.connection.state.snapshot = none) initial := by
  rw [check_query]
  change ∀ found ∈ Model.RunStep.executions (.continued (.error 1) _ []), ∀ selected,
    OutputChoice found.output selected → _
  simp only [Model.RunStep.executions, List.mem_singleton, forall_eq]
  rw [OutputChoice.forall_iff]
  decide +kernel

/-- Sending nothing retains the caller's existing index, trace and connection. -/
theorem helper_empty (state : ExecutionContext) :
    (send (⟨[]⟩ : Script)).check (fun outputs final => outputs = [] ∧ final = state) state :=
  (check_send_empty _ state).mpr ⟨rfl, rfl⟩

#print axioms helpers_tactic
#print axioms helpers_explicit
#print axioms helpers_rollback
#print axioms helper_errors
#print axioms commit_error
#print axioms helper_empty
#print axioms Sql.check_map
#print axioms check_send_empty
#print axioms check_send_append
#print axioms check_query
#print axioms check_single
#print axioms send_spec
#print axioms query_spec
#print axioms single_spec
end ExecutionExamples
