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
  let created : Database := { catalog := resolved.applyCatalog c.state.database.catalog, rows := c.state.database.rows ++ [[]] }
  have guards := step_guards_hold found rfl valid
  cases resolved <;> simp only [Resolved.Statement.createsBySchema, Bool.not_eq_true'] at creates
  all_goals try contradiction
  case createTable => exact runScriptStep_createTable_ok found valid
  case createIndex =>
    obtain ⟨pos, aligned, present⟩ := guards
    obtain ⟨table, tableAt⟩ := Option.isSome_iff_exists.mp present
    obtain ⟨out, next, step, ok, _⟩ := runScriptStep_ordinary_ok (parameters := parameters) (clock := clock)
      (index := index) (database := created) found rfl (by intro _ _ h; cases h) (value := 0) rfl
      (by rfl) (by rfl) (by simp [created, Resolved.Statement.applyCatalog, SqlState.statementRun, runStatement, Model.step, pos, aligned, tableAt, creates])
      (by rfl)
    exact ⟨out, next, step, ok⟩
  all_goals
    obtain ⟨pos, aligned⟩ := guards
    obtain ⟨out, next, step, ok, _⟩ := runScriptStep_ordinary_ok (parameters := parameters) (clock := clock)
      (index := index) (database := created) found rfl (by intro _ _ h; cases h) (value := 0) rfl
      (by rfl) (by rfl) (by simp [created, Resolved.Statement.applyCatalog, SqlState.statementRun, runStatement, Model.step, pos, aligned]) (by rfl)
    exact ⟨out, next, step, ok⟩

/-- Every resolved DROP COLUMN on a valid database continues with one successful execution.
Proof sketch: {name}`step_guards_hold` proves the whole drop guard from the catalog.
{name}`runScriptStep_ordinary_ok` then reads the successful effect. -/
theorem runScriptStep_dropColumn_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos column : Nat} {stored : Catalog} {profile : Profile}
    (found : resolveStatement context c.resolveState statement = .ok (.dropColumn pos column stored, after))
    (valid : c.state.database.Valid profile) :
    ∃ output next, runScriptStep context clock index c statement parameters = .continued output next [] ∧
      output.isError = false := by
  have runs : c.state.database.runsDropColumn pos column stored = true := step_guards_hold found rfl valid
  obtain ⟨out, next, step, ok, _⟩ := runScriptStep_ordinary_ok (parameters := parameters) (clock := clock)
    (index := index) (database := c.state.database.dropColumn pos column stored) found rfl (by intro _ _ h; cases h) (value := 0) rfl
    (by rfl) (by rfl) (by simp [SqlState.statementRun, runStatement, Model.step, runs]) (by rfl)
  exact ⟨out, next, step, ok⟩

end Belay.Sqlite.Model
