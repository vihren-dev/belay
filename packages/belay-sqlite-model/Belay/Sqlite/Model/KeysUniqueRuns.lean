import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.KeysUniqueRunStep

set_option doc.verso true

/-! Unique-key preservation evidence for generic run laws. Each reached statement meets
its run condition; a transaction's saved database also satisfies the invariant.
{lit}`KeysUniqueRunExamples` shows why the CREATE INDEX condition is necessary. -/

namespace Belay.Sqlite.Model

/-- The statement theorem of "keys unique" in the form of {name}`StatementKeeps`, for the run
condition of a statement. For every clock value, counters, parameter list, resolved statement and database:
if the database satisfies {name}`Database.KeysUnique` and the statement meets its run condition
({name}`Resolved.Statement.RunCondition`) on the database, the effect of {name}`runStatement`
satisfies {name}`Database.KeysUnique` ({name}`Effect.Satisfies`): the database of a success, and
the database that an error with {name}`ExecutionError.constraintFail` carries, satisfy it. An error
with any other reason requires nothing. Proof sketch: {name}`runStatement_keysUnique` with
{name}`Resolved.Statement.keysCondition_of_runCondition`. -/
theorem keysUnique_statementKeeps :
    StatementKeeps Database.KeysUnique fun _ _ _ statement database => statement.RunCondition database :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ unique condition =>
    runStatement_keysUnique clock counters parameters statement unique
      (Resolved.Statement.keysCondition_of_runCondition condition))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

end Belay.Sqlite.Model
