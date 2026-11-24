import Belay

set_option doc.verso true

/-! The former schema statements of ADR 0033, derived with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedSchema

/-- The deleted law {lit}`runScriptStep_noOp`. For every context, clock, statement index, connection, statement and bound values: if the
statement resolves on the connection to the no-op {lit}`.drop []` (with any resolution state after
it), then one step of it continues with the output done with zero changes, the same connection
(so the same database, transaction state and counters) and no other execution. This holds for
CREATE TABLE, CREATE INDEX, CREATE VIEW and CREATE TRIGGER with {lit}`IF NOT EXISTS` when they do
nothing. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_noOp {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop [], after)) :
    runScriptStep context clock index connection statement parameters = .continued (.done 0) connection [] := by
  simpa [Database.drop_nil, Connection.withDatabase] using runScriptStep_dropPlain_eq (parameters := parameters) (clock := clock) (index := index) found

/-- The deleted law {lit}`runScriptStep_createTable_noOp`. For every context, clock, statement index, connection, CREATE TABLE and bound values: if a
table or view has the name and the name is not reserved ({name}`createTableKept`), then one step
of the statement with {lit}`IF NOT EXISTS` continues with done and zero changes, the same
connection and no other execution, whatever the columns, constraints and options. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_createTable_noOp {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name : Identifier} {columns : List Syntax.ColumnDefinition}
    {constraints : List Syntax.TableConstraint} {options : Syntax.TableOptions} {parameters : List Value}
    (kept : createTableKept connection.state.database.catalog name = true) :
    runScriptStep context clock index connection (.createTable name columns constraints options true) parameters =
      .continued (.done 0) connection [] :=
  runScriptStep_noOp (after := { connection.resolveState with catalog := connection.state.database.catalog.drop [] })
    (by simp [statement_arms, resolveCreateTableIf, Connection.resolveState, kept, ResolveState.withCatalog, Except.map])

/-- The deleted law {lit}`runScriptStep_createIndex_noOp`. For every context, clock, statement index, connection, CREATE INDEX and bound values: if the
table exists, no name is reserved and an index has the name ({name}`createIndexKept`), then one
step of the statement with {lit}`IF NOT EXISTS` continues with done and zero changes, the same
connection and no other execution, whatever the uniqueness, terms and filter. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_createIndex_noOp {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name tableName : Identifier} {unique : Bool}
    {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr} {parameters : List Value}
    (kept : createIndexKept connection.state.database.catalog name tableName = true) :
    runScriptStep context clock index connection (.createIndex name unique tableName terms filter true) parameters =
      .continued (.done 0) connection [] :=
  runScriptStep_noOp (after := { connection.resolveState with catalog := connection.state.database.catalog.drop [] })
    (by simp [statement_arms, resolveCreateIndexIf, Connection.resolveState, kept, ResolveState.withCatalog, Except.map])

#print axioms runScriptStep_noOp
#print axioms runScriptStep_createTable_noOp
#print axioms runScriptStep_createIndex_noOp

end Belay.Sqlite.Model.ReplacedSchema
