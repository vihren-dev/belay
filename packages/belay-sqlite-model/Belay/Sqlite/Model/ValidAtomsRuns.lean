import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.ValidAtomsStatement
import Belay.Sqlite.Model.RunHolds

set_option doc.verso true

/-! Independent NOT NULL, type and CHECK preservation evidence for generic run laws.
Each atom keeps its ADD COLUMN condition. Surface callers can derive those conditions
from admission through the generic helper in {lit}`ScriptRunConstraints`. -/

namespace Belay.Sqlite.Model

/-- The statement theorem of "not null" in the form of {name}`StatementKeeps`, for the condition of
{name}`Resolved.Statement.NotNullCondition`. For every clock value, counters, parameter list, resolved statement
and database: if the database satisfies {name}`Database.NotNull` and the statement meets its condition
on the database, every admitted execution of the statement ({name}`StatementRun.effects` of
{name}`runStatement`: its own run and, for an INSERT from a query, its alternative executions) has an effect that
satisfies {name}`Database.NotNull` ({name}`Effect.Satisfies`): the database of a success, and the database that an
error with {name}`ExecutionError.constraintFail` carries, satisfy it. An error with any other reason requires
nothing. Proof sketch: {name}`runStatement_notNull` for the own run, and {name}`StatementKeeps.ofOwnRun` for the
alternative executions of an INSERT from a query. -/
theorem notNull_statementKeeps : StatementKeeps Database.NotNull fun statement database => statement.NotNullCondition database :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds condition => runStatement_notNull clock counters parameters statement holds condition)
    (fun _ _ _ _ _ _ _ _ _ h => h)

/-- The statement theorem of "types fit" in the form of {name}`StatementKeeps`, for the condition of
{name}`Resolved.Statement.TypesFitCondition`. For every clock value, counters, parameter list, resolved statement
and database: if the database satisfies {name}`Database.TypesFit` and the statement meets its condition
on the database, every admitted execution of the statement ({name}`StatementRun.effects` of
{name}`runStatement`: its own run and, for an INSERT from a query, its alternative executions) has an effect that
satisfies {name}`Database.TypesFit` ({name}`Effect.Satisfies`): the database of a success, and the database that an
error with {name}`ExecutionError.constraintFail` carries, satisfy it. An error with any other reason requires
nothing. Proof sketch: {name}`runStatement_typesFit` for the own run, and {name}`StatementKeeps.ofOwnRun` for the
alternative executions of an INSERT from a query. -/
theorem typesFit_statementKeeps : StatementKeeps Database.TypesFit fun statement database => statement.TypesFitCondition database :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds condition => runStatement_typesFit clock counters parameters statement holds condition)
    (fun _ _ _ _ _ _ _ _ _ h => h)

/-- The statement theorem of "checks hold" in the form of {name}`StatementKeeps`, for the condition of
{name}`Resolved.Statement.ChecksHoldCondition`. For every clock value, counters, parameter list, resolved statement
and database: if the database satisfies {name}`Database.ChecksHold` and the statement meets its condition
on the database, every admitted execution of the statement ({name}`StatementRun.effects` of
{name}`runStatement`: its own run and, for an INSERT from a query, its alternative executions) has an effect that
satisfies {name}`Database.ChecksHold` ({name}`Effect.Satisfies`): the database of a success, and the database that an
error with {name}`ExecutionError.constraintFail` carries, satisfy it. An error with any other reason requires
nothing. Proof sketch: {name}`runStatement_checksHold` for the own run, and {name}`StatementKeeps.ofOwnRun` for the
alternative executions of an INSERT from a query. -/
theorem checksHold_statementKeeps : StatementKeeps Database.ChecksHold fun statement database => statement.ChecksHoldCondition database :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds condition => runStatement_checksHold clock counters parameters statement holds condition)
    (fun _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
