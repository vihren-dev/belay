import Belay.Sqlite.Model.Programs.Scripts.StepContinuesOk
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
  · exact runScriptStep_setting_ok resolution
  · exact runScriptStep_drop_ok resolution
  · apply runScriptStep_begin_ok resolution
    simpa [Connection.resolveState] using checked
  · simp only [Bool.and_eq_true] at checked
    obtain ⟨open_, _⟩ := checked
    cases snapshot : c.state.snapshot with
    | none => simp [Connection.resolveState, snapshot] at open_
    | some original => exact runScriptStep_commit_ok resolution snapshot
  · exact runScriptStep_rewrite_ok resolution valid.1
  · exact runScriptStep_dropColumn_ok resolution valid.1
  · obtain ⟨table, _, accepts⟩ := List.any_eq_true.mp checked
    simp only [Bool.and_eq_true] at accepts
    obtain ⟨kind, ordered⟩ := accepts
    rw [eq_of_beq kind] at resolution
    obtain ⟨_, rows⟩ := Database.keyCheckRows_modeled ordered
    obtain ⟨output, step, ok⟩ := runScriptStep_keyCheck_resolved (clock := clock) (index := index)
      (parameters := parameters) resolution rows
    exact ⟨output, _, step, ok⟩
  all_goals first | exact runScriptStep_create_ok resolution checked valid.1 | contradiction

end Belay.Sqlite.Model
