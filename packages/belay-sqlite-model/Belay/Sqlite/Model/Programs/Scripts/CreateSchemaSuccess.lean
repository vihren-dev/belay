import Belay.Sqlite.Model.Programs.Scripts.CreateObjectRules
import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule
import Belay.Sqlite.Model.Programs.Scripts.OrdinaryStepOk

set_option doc.verso true

/-! The schema-only script check uses these step laws for catalog creations and DROP COLUMN. -/

namespace Belay.Sqlite.Model

/-- Whether a resolved statement creates an object with no condition on the stored rows.
CREATE TABLE, VIEW, TRIGGER and a non-unique index qualify. A UNIQUE index needs its own row check. -/
def Resolved.Statement.createsBySchema : Resolved.Statement → Bool
  | .createTable .. | .createView .. | .createTrigger .. => true
  | .createIndex _ _ key => !key.unique
  | .addColumn .. | .dropColumn .. | .drop .. | .rewrite .. | .begin | .commit | .rollback | .insert ..
  | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting .. => false

/-- Each resolved creation that passes {name}`Resolved.Statement.createsBySchema` succeeds on every
valid input database. The script step continues with a non-error output and has no alternative execution.
Proof sketch: the resolver and validity supply the append position, row alignment and index table.
For each kind of creation the ordinary step then stores the extended database. -/
theorem runScriptStep_create_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c : Connection} {statement : Syntax.Statement} {parameters : List Value} {resolved : Resolved.Statement}
    {after : ResolveState} {profile : Profile}
    (found : resolveStatement context c.resolveState statement = .ok (resolved, after))
    (creates : resolved.createsBySchema = true) (valid : c.state.database.Valid profile) :
    ∃ output next, runScriptStep context clock index c statement parameters = .continued output next [] ∧
      output.isError = false := by
  have guards := step_guards_hold found rfl valid
  cases resolved <;> simp only [Resolved.Statement.createsBySchema, Bool.not_eq_true'] at creates
  all_goals try contradiction
  case createTable =>
    obtain ⟨atEnd, aligned⟩ := guards
    simp [runScriptStep_createTable_eq found, atEnd, aligned, Output.isError]
  case createIndex =>
    obtain ⟨pos, aligned, present⟩ := guards
    obtain ⟨table, tableAt⟩ := Option.isSome_iff_exists.mp present
    simp [runScriptStep_createIndex_eq found, pos, aligned, tableAt, creates, Output.isError]
  case createView =>
    obtain ⟨pos, aligned⟩ := guards
    simp [runScriptStep_createView_eq found, pos, aligned, Output.isError]
  case createTrigger =>
    obtain ⟨pos, aligned⟩ := guards
    simp [runScriptStep_createTrigger_eq found, pos, aligned, Output.isError]

end Belay.Sqlite.Model
