import Belay.Sqlite.Model.Programs.Scripts.CatalogChangeRules
import Belay.Sqlite.Model.Programs.Scripts.ControlRules
import Belay.Sqlite.Model.Programs.Scripts.FailedStepFrame
import Belay.Sqlite.Model.Programs.Scripts.StepContinues
import Belay.Sqlite.Model.Programs.Scripts.ResolvedStepGuards
import Belay.Sqlite.Model.Programs.Scripts.CreateSchemaSuccess
import Belay.Sqlite.Model.Programs.Scripts.SchemaKeyCheck

set_option doc.verso true

/-! Certify one successful statement from its input resolution state alone. -/

namespace Belay.Sqlite.Model

/-- Check whether the schema alone guarantees one successful step for every valid
connection with this resolution state. A BEGIN needs an idle connection. A COMMIT
needs a transaction and disabled foreign-key enforcement. A plain DROP, a setting,
a resolved rewrite, a resolved DROP COLUMN and creations accepted by
{name}`Resolved.Statement.createsBySchema` qualify.
A foreign-key check qualifies when its result row order is determined for every
database. A false value gives no conclusion. -/
def Resolved.Statement.succeedsBySchema (statement : Resolved.Statement) (state : ResolveState) : Bool :=
  match statement with
  | .setting .. | .drop _ none => true
  | .begin => state.saved.isNone
  | .commit => state.saved.isSome && !state.foreignKeys
  | .rewrite .. | .dropColumn .. => true
  | .query .. =>
    (none :: (List.range state.catalog.length).map some).any fun table =>
      statement == keyCheckQuery table && state.catalog.keyCheckOrdered table
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. => statement.createsBySchema
  | .addColumn ..
  | .rollback | .drop _ (some _) | .insert .. | .insertSelect .. | .update .. | .delete ..
  | .upsert .. | .prepareError _ => false

/-- For every valid connection and every statement that resolves, a successful
{name}`Resolved.Statement.succeedsBySchema` check guarantees that the step continues
with one execution and a non-error output. No premise concerns the stored row values.
Proof sketch: apply the success rule of the resolved statement. Validity gives the
row-store length for CREATE TABLE. The bound on contributing tables makes the result
of each admitted foreign-key check available even when it contains violations. -/
theorem runScriptStep_succeedsBySchema {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState}
    (valid : c.state.Holds (Database.Valid Profile.pinned))
    (resolution : resolveStatement context c.resolveState statement = .ok (resolved, after))
    (checked : resolved.succeedsBySchema c.resolveState = true) :
    ∃ output next, runScriptStep context clock index c statement parameters = .continued output next [] ∧
      output.isError = false := by
  unfold Resolved.Statement.succeedsBySchema at checked
  split at checked
  · rw [runScriptStep_setting_eq resolution]
    exact ⟨_, _, rfl, rfl⟩
  · rw [runScriptStep_dropPlain_eq resolution]; exact ⟨_, _, rfl, rfl⟩
  · rw [runScriptStep_begin_eq resolution]
    cases snapshot : c.state.snapshot with
    | none => exact ⟨_, _, rfl, rfl⟩
    | some _ => simp [Connection.resolveState, snapshot] at checked
  · simp only [Bool.and_eq_true] at checked
    obtain ⟨open_, _⟩ := checked
    cases snapshot : c.state.snapshot with
    | none => simp [Connection.resolveState, snapshot] at open_
    | some original => rw [runScriptStep_commit_eq resolution, snapshot]; exact ⟨_, _, rfl, rfl⟩
  · simp only [runScriptStep_rewrite_eq resolution, show _ = true from step_guards_hold resolution rfl valid.1, ite_true]
    exact ⟨_, _, rfl, rfl⟩
  · simp only [runScriptStep_dropColumn_eq resolution, show _ = true from step_guards_hold resolution rfl valid.1, ite_true]
    exact ⟨_, _, rfl, rfl⟩
  · obtain ⟨table, _, accepts⟩ := List.any_eq_true.mp checked
    simp only [Bool.and_eq_true] at accepts
    obtain ⟨kind, ordered⟩ := accepts
    rw [eq_of_beq kind] at resolution
    obtain ⟨actualRows, found⟩ := Database.keyCheckRows_modeled ordered
    have out := runScriptStep_output context clock index c statement parameters
    rw [resolution] at out
    simp only [] at out
    rw [resolvedStepOutput_keyCheck_clock] at out
    obtain ⟨noError, modeled⟩ := resolvedStepOutput_keyCheck_rows index c parameters table actualRows found
    cases step : runScriptStep context clock index c statement parameters with
    | ended reason =>
      rw [step] at out
      exact absurd out.symm (modeled reason)
    | continued output next others =>
      rw [step] at out
      obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps resolution (.inl ⟨_, _, rfl⟩) step
      exact ⟨output, _, rfl, by rw [show output = _ from out]; exact noError⟩
  all_goals first | exact runScriptStep_create_ok resolution checked valid.1 | contradiction

end Belay.Sqlite.Model
