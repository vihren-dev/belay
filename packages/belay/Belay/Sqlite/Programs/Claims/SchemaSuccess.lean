import Belay.Sqlite.Programs.Claims.SendStatementsSuccess
import Belay.Sqlite.Programs.Claims.SuccessSyntax
import Belay.Sqlite.Model.Programs.Scripts.SchemaSuccessPath

set_option doc.verso true

/-! Certify schema-only migrations and let a mixed migration supply the remaining row proofs. -/

namespace Belay.Sqlite
open Model

/-- For every resolved script, a valid connection with its initial state, and a caller's
invariant that holds initially, the script succeeds if each successful step preserves
the invariant and each position in {name}`ResolveState.uncheckedSteps` is known to
continue with no error in any execution. For other positions the schema certifies
success. Both premises apply only at the corresponding schema prefix and invariant.
Proof sketch: carry the schema prefix with the caller's invariant. Use the
single-statement schema rule or the caller's success proof at each position. -/
theorem sendStatements_succeeds_mixed {statements : List (Syntax.Statement × List Value)}
    {initial final : ResolveState} {path : List Resolved.Statement} {c : Connection}
    (checked : resolveFrom runContext 0 initial (statements.map Prod.fst) = .ok (path, final))
    (clock : Option Clock) (index : Nat) (start : c.resolveState = initial)
    (valid : c.state.Holds (Database.Valid Profile.pinned)) (Inv : Nat → Connection → Prop) (base : Inv 0 c)
    (preserve : ∀ (n : Nat) (bound : n < statements.length) i (conn : Connection),
      conn.resolveState = initial.atPrefix path n → conn.state.Holds (Database.Valid Profile.pinned) → Inv n conn →
      ∀ output next others, runScriptStep runContext clock i conn statements[n].1 statements[n].2 =
        .continued output next others → ∀ found ∈ (RunStep.continued output next others).executions,
        found.output.isError = false → Inv (n + 1) found.next)
    (remaining : ∀ (n : Nat) (bound : n < statements.length), n ∈ initial.uncheckedSteps path →
      ∀ i (conn : Connection), conn.resolveState = initial.atPrefix path n →
        conn.state.Holds (Database.Valid Profile.pinned) → Inv n conn →
        ∃ output next others, runScriptStep runContext clock i conn statements[n].1 statements[n].2 =
          .continued output next others ∧ ∀ found ∈ (RunStep.continued output next others).executions,
          found.output.isError = false) : (sendStatements statements).SucceedsFrom clock index c := by
  apply sendStatements_succeedsFrom statements
    (fun n conn => conn.resolveState = initial.atPrefix path n ∧ Inv n conn) clock index c valid ⟨start, base⟩
  intro n bound i conn admitted held
  have atStmt : (statements.map Prod.fst)[n]? = some statements[n].1 := by simp [bound]
  obtain ⟨r, atR, resolution⟩ := resolveFrom_atPrefix checked atStmt
  rw [← held.1] at resolution
  have success : ∃ output next others, runScriptStep runContext clock i conn statements[n].1 statements[n].2 =
      .continued output next others ∧ ∀ found ∈ (RunStep.continued output next others).executions,
      found.output.isError = false := by
    cases flag : r.succeedsBySchema (initial.atPrefix path n) with
    | false => exact remaining n bound (ResolveState.mem_uncheckedSteps atR flag) i conn held.1 admitted held.2
    | true =>
      rw [← held.1] at flag
      obtain ⟨output, next, step, ok⟩ := runScriptStep_succeedsBySchema (clock := clock) (index := i)
        (parameters := statements[n].2) admitted resolution flag
      exact ⟨output, next, [], step, by simpa [RunStep.executions] using ok⟩
  obtain ⟨output, next, others, step, all⟩ := success
  refine ⟨output, next, others, step, fun found member => ?_⟩
  have ok := all found member
  exact ⟨ok, runScriptStep_resolveState resolution step member ok,
    preserve n bound i conn held.1 admitted held.2 output next others step found member ok⟩

/-- Check that the script resolves on the given schema and every step passes the
single-statement success check. A false result leaves the success claim open. -/
def Script.succeedsBySchema (script : Script) (schema : Database) : Bool :=
  let initial := schema.raw.connection.resolveState
  match resolveFrom runContext 0 initial (script.statements.map Prod.fst) with
  | .ok (path, _) => (initial.uncheckedSteps path).isEmpty
  | .error _ => false

/-- A script that passes {name}`Script.succeedsBySchema` succeeds on every database
of the given schema, for each complete environment. Use kernel evaluation for a
concrete schema and migration. Proof sketch: the mixed-script law has an empty
list of row-dependent positions and needs only the trivial invariant. -/
theorem Script.succeeds_of_schema {script : Script} {schema : Database}
    (check : script.succeedsBySchema schema = true) : Succeeds script (·.HasCatalog schema) := by
  simp only [Script.succeedsBySchema] at check
  split at check <;> try contradiction
  rename_i path final checked
  intro db pre env complete
  have start : (db.raw.connection env.counters).resolveState = schema.raw.connection.resolveState := by
    simp [Database.Raw.connection, Connection.resolveState, Database.HasCatalog] at pre ⊢
    exact pre
  apply sendStatements_succeeds_mixed checked env.clock 0 start
    ⟨db.valid, fun _ saved => by simp [Database.Raw.connection] at saved⟩ (fun _ _ => True) trivial
  · intros; trivial
  · intro n bound mem
    simp [List.isEmpty_iff.mp check] at mem

end Belay.Sqlite
