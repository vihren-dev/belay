import Belay.Sqlite.Model.Programs.Scripts.InsertSelectAlternatives
import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects
import Belay.Sqlite.Model.Programs.Scripts.StepRuleAttr

set_option doc.verso true

/-! The exact kind rule of CREATE TABLE. A client derives each fact about the step of a CREATE TABLE, such as its
output, the next connection or the absence of a further execution, from the one equation of
{lit}`runScriptStep_createTable_eq` and a case split on its condition. -/

namespace Belay.Sqlite.Model

/-- The kind rule of CREATE TABLE. For every resolution context, clock, index, connection, statement, parameter
values, resolution state, target position, name and table definition: if the statement resolves from the
connection to CREATE TABLE of the table with the name at the target position, the step of the statement is
exactly this:
* When the target position is the length of the catalog of the database and the database has one row list for
  each catalog object, the step continues with output {lean}`Output.done 0`, with the connection whose database
  is the database after CREATE TABLE ({name}`Database.createTable`) and with nothing else changed
  ({name}`Connection.withDatabase`), and with no further execution.
* Otherwise the run ends with the reason {name}`unmodeledHere`.
The rule has no premise about the clock, the counters or the settings: CREATE TABLE reads neither the clock nor a
counter, counts nothing, and keeps the settings. A valid database satisfies the second condition, and the resolver
gives the end of the catalog as the target. Proof sketch: unfold the step with the resolution; the effect is
{name}`step` of CREATE TABLE, which succeeds exactly under the two conditions and else fails as unmodeled; the
counts are the default ({name}`Counters.apply_default`), and the resolution certificate keeps the settings. -/
@[step_rule] theorem runScriptStep_createTable_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {name : Identifier} {table : CatalogTable}
    (found : resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after)) :
    runScriptStep context clock index connection statement parameters =
      if target = connection.state.database.catalog.length ∧
          connection.state.database.rows.length = connection.state.database.catalog.length then
        .continued (.done 0) (connection.withDatabase (connection.state.database.createTable name table)) []
      else .ended unmodeledHere := by
  have ordinary : (Resolved.Statement.createTable target name table).isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  have reads : (Resolved.Statement.createTable target name table).clockExpressions = [] := rfl
  have quiet : (Resolved.Statement.createTable target name table).readsClock = false := rfl
  simp only [runScriptStep, runScriptStepWith, found, ranScriptStep, statementClock, quiet,
    Resolved.Statement.counterReads, reads, List.any_nil,
    advanceRun_ordinary index _ connection.state _ ordinary, SqlState.statementRun, runStatement, Model.step]
  by_cases guard : target = connection.state.database.catalog.length ∧
      connection.state.database.rows.length = connection.state.database.catalog.length
  · simp [guard, SqlState.publish, SqlTransition.counted, Output.ofStep, haltError, statementOutput,
      Resolved.Statement.returnsRows, StatementExecution.ofAlternatives, RunStep.withOthers, Connection.afterStep,
      Connection.withDatabase, Database.createTable, Counters.apply_default, same, Connection.resolveState]
    rfl
  · simp [guard, SqlState.publish, SqlTransition.counted, Output.ofStep, haltError_failed]

end Belay.Sqlite.Model
