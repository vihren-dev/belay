import Belay.Sqlite.Model.ScriptRun
import Belay.Sqlite.Model.Resolution.StatementArms

set_option doc.verso true

/-! The step laws of {lit}`IF NOT EXISTS` on CREATE TABLE and CREATE INDEX (ADR 0030, D3): when
the name does not make the statement a no-op, the clause changes nothing. -/

namespace Belay.Sqlite.Model

/-- For every context, clock, statement index, connection, bound values and two statements
that resolve to the same result on the connection, one step of each is the same. Proof
sketch: a step reads its statement only through {name}`resolveStatement`. -/
theorem runScriptStep_congr_resolve {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {first second : Syntax.Statement} {parameters : List Value}
    (same : resolveStatement context connection.resolveState first =
      resolveStatement context connection.resolveState second) :
    runScriptStep context clock index connection first parameters =
      runScriptStep context clock index connection second parameters := by
  simp only [runScriptStep, runScriptStepWith, same]

/-- For every context, clock, statement index, connection, CREATE TABLE and bound values: if
no table or view has the name, or the name is reserved ({name}`createTableKept` is false),
then one step of the statement with {lit}`IF NOT EXISTS` is the step without it. Proof
sketch: both resolve with {name}`resolveCreateTable`. -/
theorem runScriptStep_createTable_ifNotExists_free {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name : Identifier} {columns : List Syntax.ColumnDefinition}
    {constraints : List Syntax.TableConstraint} {options : Syntax.TableOptions} {parameters : List Value}
    (free : createTableKept connection.state.database.catalog name = false) :
    runScriptStep context clock index connection (.createTable name columns constraints options true) parameters =
      runScriptStep context clock index connection (.createTable name columns constraints options) parameters :=
  runScriptStep_congr_resolve (by
    simp [statement_arms, resolveCreateTableIf, Connection.resolveState, free])

/-- For every context, clock, statement index, connection, CREATE INDEX and bound values: if
{name}`createIndexKept` is false (the table is missing, a name is reserved, or no index has
the name), then one step of the statement with {lit}`IF NOT EXISTS` is the step without it.
Proof sketch: both resolve with {name}`resolveCreateIndex`. -/
theorem runScriptStep_createIndex_ifNotExists_free {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name tableName : Identifier} {unique : Bool}
    {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr} {parameters : List Value}
    (free : createIndexKept connection.state.database.catalog name tableName = false) :
    runScriptStep context clock index connection (.createIndex name unique tableName terms filter true) parameters =
      runScriptStep context clock index connection (.createIndex name unique tableName terms filter) parameters :=
  runScriptStep_congr_resolve (by
    simp [statement_arms, resolveCreateIndexIf, Connection.resolveState, free])

end Belay.Sqlite.Model
