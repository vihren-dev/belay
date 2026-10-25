import ExecutionBranches
import Belay.Sqlite.ProgramSuccess
import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.ExecutionWPLaws
import Std.Tactic.Do

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionExamples
open Belay.Sqlite Std.Do

/-- A nontrivial SQL write returns the number of statement outputs. -/
def writeOne : Sql Nat := do
  let outputs ← send (sql r"INSERT INTO t VALUES (3, 3)")
  pure outputs.length

/-- From the fixture context, the write returns one output and leaves three rows. -/
@[spec] theorem writeOne_spec :
    ⦃fun state : ExecutionContext => ⌜state = initial⌝⦄ writeOne
      ⦃⇓ value state => ⌜value = 1 ∧ (state.connection.state.database.rowsAt 0).length = 3⌝⦄ := by
  intro state same
  cases same
  change writeOne.check (fun value state => value = 1 ∧ (state.connection.state.database.rowsAt 0).length = 3) initial
  decide +kernel

/-- A result-dependent continuation adds three to the write's returned count. -/
def addThree : Sql Nat := do
  let value ← writeOne
  pure (value + 3)

/-- The standard verification-condition tactic uses the SQL operation's checked rule. -/
theorem tactic_triple :
    ⦃fun state : ExecutionContext => ⌜state = initial⌝⦄ addThree ⦃⇓ value _ => ⌜value = 4⌝⦄ := by
  unfold addThree
  mvcgen <;> simp_all

/-- Explicit pure/bind rules prove the same claim without experimental automation. -/
theorem explicit_triple :
    ⦃fun state : ExecutionContext => ⌜state = initial⌝⦄ addThree ⦃⇓ value _ => ⌜value = 4⌝⦄ := by
  apply Triple.bind (m := Sql) (ps := .arg ExecutionContext .pure) writeOne (fun value => pure (value + 3))
    (Q := fun (value : Nat) (state : ExecutionContext) =>
      ⌜value = 1 ∧ (state.connection.state.database.rowsAt 0).length = 3⌝)
  · exact writeOne_spec
  · intro value
    apply Triple.pure
    intro state holds
    simp [holds.1]

/-- A modeled error continues to a write, so it can still establish a final row count. -/
theorem error_then_write :
    (send (sql r"SELECT absent FROM missing; INSERT INTO t VALUES (3, 3)")).check
      (fun _ state => state.index = 2 ∧ state.outputs.allOk = false ∧
        (state.connection.state.database.rowsAt 0).length = 3) initial := by decide +kernel

/-- A modeled error followed by an unmodeled statement still falsifies a true postcondition. -/
theorem error_then_unmodeled :
    ¬ (send (sql r"SELECT absent FROM missing; SELECT random()")).check (fun _ _ => True) initial := by
  decide +kernel

/-- An alternative rows result selects an unmodeled continuation; the actual branch succeeds. -/
def alternateStops : Sql (List Output) := do
  match ← single (sql r"SELECT x FROM t LIMIT 1") with
  | some (.integer 1) => pure []
  | _ => send (sql r"SELECT random()")

/-- Actual modeled execution alone does not establish a transformer over all branches. -/
theorem alternate_is_required :
    (sample.run alternateStops daily).value.isSome = true ∧
      ¬ alternateStops.check (fun _ _ => True) initial := by decide +kernel

/-- The raw wrapper selects an unmodeled continuation even though each concrete rows branch returns. -/
def rawStops : Sql Unit :=
  let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values fun output => match output with
    | .oneOf _ => (send (sql r"SELECT random()")).map fun _ => ()
    | .done _ | .rows _ | .error _ | .unmodeled _ => .pure ()

/-- Concrete rows obligations cannot replace the raw continuation obligation. -/
theorem raw_is_required : ¬ rawStops.check (fun _ _ => True) initial := by decide +kernel

/-- Two time reads use consecutive indices; bind does not reset the environment. -/
theorem clock_advances :
    (do
      let first ← single (sql r"SELECT CURRENT_TIMESTAMP")
      let second ← single (sql r"SELECT CURRENT_TIMESTAMP")
      pure (first, second)).check (fun value state =>
        value = (some (("2025-01-01 00:00:00" : String) : Value),
          some (("2025-01-02 00:00:00" : String) : Value)) ∧ state.index = 2) initial := by
  decide +kernel

/-- A write's counters remain available to the next statement across bind. -/
theorem counter_survives :
    (do
      let _ ← send (sql r"INSERT INTO t VALUES (3, 3)")
      single (sql r"SELECT changes()")).check
      (fun value state => value = some 1 ∧ state.connection.state.counters.changes = some 1) initial := by
  decide +kernel

/-- An open transaction survives bind and rollback restores its snapshot before a query. -/
theorem rollback_survives :
    (do
      let _ ← send (sql r"BEGIN; INSERT INTO t VALUES (3, 3)")
      let _ ← send (sql r"ROLLBACK")
      single (sql r"SELECT count(*) FROM t")).check
      (fun value state => value = some 2 ∧ state.connection.state.snapshot = none) initial := by
  decide +kernel

/-- Existing error outputs remain in a pure program's postcondition context. -/
theorem prefix_is_retained :
    (Sql.pure ()).check (fun _ state => state.outputs.allOk = false)
      { initial with outputs := [.error 1] } := by decide +kernel

#print axioms writeOne_spec
#print axioms tactic_triple
#print axioms explicit_triple
#print axioms error_then_write
#print axioms error_then_unmodeled
#print axioms alternate_is_required
#print axioms raw_is_required
#print axioms clock_advances
#print axioms counter_survives
#print axioms rollback_survives
#print axioms prefix_is_retained
#print axioms Sql.check_and
#print axioms Sql.check_bind
#print axioms Sql.check_actual
#print axioms Sql.check_exec
#print axioms sqlWPMonad
#print axioms Sql.triple_branch
#print axioms Sql.triple_actual
end ExecutionExamples
