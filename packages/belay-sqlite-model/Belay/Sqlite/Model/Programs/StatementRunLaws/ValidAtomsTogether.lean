import Belay.Sqlite.Model.Programs.StatementRunLaws.ValidAtomsStatement
import Belay.Sqlite.Model.Programs.StatementRunLaws.KeysUniqueRuns
import Belay.Sqlite.Model.Schema.Rows.ValidAtomsTogether

set_option doc.verso true

/-! The conjunction of NOT NULL, type, CHECK and unique-key invariants, with their
combined statement condition and preservation evidence. Generic run laws lift that evidence;
{lit}`ScriptRunConstraints` derives surface conditions from admission and resolution. -/

namespace Belay.Sqlite.Model

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
    StatementKeeps Database.ConstraintAtoms fun _ _ _ statement database => statement.AtomsCondition database :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ atoms condition =>
    Effect.satisfies_and (runStatement_notNull clock counters parameters statement atoms.1 condition.2.1)
      (runStatement_typesFit clock counters parameters statement atoms.2.1 condition.2.2.1)
      (runStatement_checksHold clock counters parameters statement atoms.2.2.1 condition.2.2.2)
      (runStatement_keysUnique clock counters parameters statement atoms.2.2.2
        (Resolved.Statement.keysCondition_of_runCondition condition.1)))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
