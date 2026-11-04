import Belay.Sqlite.Model.CreateIndexSuccessLaws
import Belay.Sqlite.Model.DropTableStepLaws

set_option doc.verso true

/-! The step laws of {lit}`IF NOT EXISTS` on the CREATE statements (ADR 0030, D3 and D7): a
statement that resolves to the no-op {lit}`.drop []` outputs done with zero changes and keeps the
connection, and when the name does not make CREATE TABLE or CREATE INDEX a no-op, the clause
changes nothing. -/

namespace Belay.Sqlite.Model

/-- Every entry is unchanged by a drop of no positions. -/
theorem CatalogEntry.afterDrop_nil (entry : CatalogEntry) : entry.afterDrop [] = entry := by
  have all (list : List Nat) : list.filter (fun _ => true) = list := List.filter_eq_self.mpr fun _ _ => rfl
  cases entry <;> simp [CatalogEntry.afterDrop, keptBelow, all]

/-- Every catalog is unchanged by a drop of no positions. -/
theorem Catalog.drop_nil (catalog : Catalog) : catalog.drop [] = catalog := by
  have all : catalog.zipIdx.filter (fun _ => true) = catalog.zipIdx := List.filter_eq_self.mpr fun _ _ => rfl
  simp only [Catalog.drop, List.contains_nil, Bool.not_false, all, CatalogEntry.afterDrop_nil]
  conv => rhs; rw [← List.zipIdx_map_fst 0 catalog]

/-- Every database is unchanged by a drop of no positions. -/
theorem Database.drop_nil (database : Database) : database.drop [] = database := by
  have all : database.rows.zipIdx.filter (fun _ => true) = database.rows.zipIdx :=
    List.filter_eq_self.mpr fun _ _ => rfl
  simp [Database.drop, Catalog.drop_nil, all, List.zipIdx_map_fst]

/-- For every context, clock, statement index, connection, statement and bound values: if the
statement resolves on the connection to the no-op {lit}`.drop []` (with any resolution state after
it), then one step of it continues with the output done with zero changes, the same connection
(so the same database, transaction state and counters) and no other execution. This holds for
CREATE TABLE, CREATE INDEX, CREATE VIEW and CREATE TRIGGER with {lit}`IF NOT EXISTS` when they do
nothing. Proof sketch: {name}`resolvedStepOutput_drop_nil` gives the output, and
{name}`runScriptStep_drop_plain` with {name}`Database.drop_nil` the connection. -/
theorem runScriptStep_noOp {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop [], after)) :
    runScriptStep context clock index connection statement parameters = .continued (.done 0) connection [] := by
  have out : (runScriptStep context clock index connection statement parameters).output = .done 0 := by
    rw [runScriptStep_output, found]; exact resolvedStepOutput_drop_nil clock index connection parameters
  cases step : runScriptStep context clock index connection statement parameters with
  | ended reason => simp [step, RunStep.output] at out
  | continued output next others =>
    obtain ⟨-, rfl, nextEq⟩ := runScriptStep_drop_plain found step
    simp only [step, RunStep.output] at out
    rw [out, nextEq, Database.drop_nil]

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

/-- For every context, clock, statement index, connection, CREATE TABLE and bound values: if a
table or view has the name and the name is not reserved ({name}`createTableKept`), then one step
of the statement with {lit}`IF NOT EXISTS` continues with done and zero changes, the same
connection and no other execution, whatever the columns, constraints and options. Proof
sketch: the statement resolves to {lit}`.drop []`; {name}`runScriptStep_noOp`. -/
theorem runScriptStep_createTable_noOp {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name : Identifier} {columns : List Syntax.ColumnDefinition}
    {constraints : List Syntax.TableConstraint} {options : Syntax.TableOptions} {parameters : List Value}
    (kept : createTableKept connection.state.database.catalog name = true) :
    runScriptStep context clock index connection (.createTable name columns constraints options true) parameters =
      .continued (.done 0) connection [] :=
  runScriptStep_noOp (after := { connection.resolveState with catalog := connection.state.database.catalog.drop [] })
    (by simp [statement_arms, resolveCreateTableIf, Connection.resolveState, kept, ResolveState.withCatalog, Except.map])

/-- For every context, clock, statement index, connection, CREATE INDEX and bound values: if the
table exists, no name is reserved and an index has the name ({name}`createIndexKept`), then one
step of the statement with {lit}`IF NOT EXISTS` continues with done and zero changes, the same
connection and no other execution, whatever the uniqueness, terms and filter. Proof sketch: the
statement resolves to {lit}`.drop []`; {name}`runScriptStep_noOp`. -/
theorem runScriptStep_createIndex_noOp {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name tableName : Identifier} {unique : Bool}
    {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr} {parameters : List Value}
    (kept : createIndexKept connection.state.database.catalog name tableName = true) :
    runScriptStep context clock index connection (.createIndex name unique tableName terms filter true) parameters =
      .continued (.done 0) connection [] :=
  runScriptStep_noOp (after := { connection.resolveState with catalog := connection.state.database.catalog.drop [] })
    (by simp [statement_arms, resolveCreateIndexIf, Connection.resolveState, kept, ResolveState.withCatalog, Except.map])

end Belay.Sqlite.Model
