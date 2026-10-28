import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.ValidAtomsStatement
import Belay.Sqlite.Model.KeysUniqueRuns

set_option doc.verso true

/-! The conjunction of NOT NULL, type, CHECK and unique-key invariants, with their
combined statement condition and preservation evidence. Generic run laws lift that evidence;
{lit}`ScriptRunConstraints` derives surface conditions from admission and resolution. -/

namespace Belay.Sqlite.Model

/-- For the given database: it satisfies the four constraint atoms of {name}`Database.Valid`, each
for its own reading: {name}`Database.NotNull`, {name}`Database.TypesFit`, {name}`Database.ChecksHold`
and {name}`Database.KeysUnique`. It leaves out the facts of {name}`Database.Admitted`. -/
def Database.ConstraintAtoms (database : Database) : Prop :=
  database.NotNull ∧ database.TypesFit ∧ database.ChecksHold ∧ database.KeysUnique

/-- For every profile and database: a valid database ({name}`Database.Valid`) satisfies
{name}`Database.ConstraintAtoms`. Proof sketch: the four fields of the structure. -/
theorem Database.Valid.constraintAtoms {profile : Profile} {database : Database} (valid : database.Valid profile) :
    database.ConstraintAtoms :=
  ⟨valid.notNull, valid.typesFit, valid.check, valid.unique⟩

/-- The condition of a statement on the database for the four atoms together: the run condition of
"keys unique" ({name}`Resolved.Statement.RunCondition`: CREATE INDEX, ADD COLUMN and DROP) and the
conditions of "not null", "types fit" and "checks hold" for ADD COLUMN. All four hold. -/
def Resolved.Statement.AtomsCondition (database : Database) (statement : Resolved.Statement) : Prop :=
  statement.RunCondition database ∧ statement.NotNullCondition database ∧ statement.TypesFitCondition database ∧
    statement.ChecksHoldCondition database

/-- For every database and statement: if the statement has no run condition
({name}`Resolved.Statement.unconditioned`: it is not CREATE INDEX, ADD COLUMN or DROP), it meets
{name}`Resolved.Statement.AtomsCondition` on the database. Proof sketch: a case split on the
statement; each remaining case has four conditions that are {lit}`True`. -/
theorem Resolved.Statement.atomsCondition_of_unconditioned {database : Database} :
    ∀ {statement : Resolved.Statement}, statement.unconditioned = true → statement.AtomsCondition database := by
  intro statement unconditioned
  cases statement <;> first | exact ⟨trivial, trivial, trivial, trivial⟩ | exact nomatch unconditioned

/-- The statement theorem of the four atoms together, in the form of {name}`StatementKeeps`, for the
condition {name}`Resolved.Statement.AtomsCondition`. For every clock value, counters, parameter list,
resolved statement and database: if the database satisfies {name}`Database.ConstraintAtoms` and the
statement meets its condition on the database, the effect of {name}`runStatement` satisfies
{name}`Database.ConstraintAtoms` ({name}`Effect.Satisfies`): the database of a success, and the
database that an error with {name}`ExecutionError.constraintFail` carries, satisfy it. An error with
any other reason requires nothing. Proof sketch: {name}`Effect.satisfies_and` of
{name}`runStatement_notNull`, {name}`runStatement_typesFit`, {name}`runStatement_checksHold` and
{name}`runStatement_keysUnique`. -/
theorem constraintAtoms_statementKeeps :
    StatementKeeps Database.ConstraintAtoms fun statement database => statement.AtomsCondition database :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ atoms condition =>
    Effect.satisfies_and (runStatement_notNull clock counters parameters statement atoms.1 condition.2.1)
      (runStatement_typesFit clock counters parameters statement atoms.2.1 condition.2.2.1)
      (runStatement_checksHold clock counters parameters statement atoms.2.2.1 condition.2.2.2)
      (runStatement_keysUnique clock counters parameters statement atoms.2.2.2
        (Resolved.Statement.keysCondition_of_runCondition condition.1)))
    (fun _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
