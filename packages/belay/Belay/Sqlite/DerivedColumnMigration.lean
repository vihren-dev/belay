import Belay.Sqlite.MigrationPatternFresh
import Belay.Sqlite.MigrationPatternAfter
import Belay.Sqlite.SendStatementsBranches
import Belay.Sqlite.SingleStatementObservations
import Belay.Sqlite.ScriptSuccess

set_option doc.verso true

/-! A migration that adds a column, backfills it from an expression and registers triggers (ADR 0017,
S6), as a migration pattern. A read that returns old columns keeps its result when its filter moves from
the expression to the stored column, as long as the two filters keep the same rows of the migrated table;
a read that does not read the new column is preserved. The theorems quantify over the table, the column
definition, the written expression, the triggers and the statements of the reads. The guide's lowercase
expansion is one instance. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The migration script for the table {lit}`tableName`: ADD COLUMN of {lit}`definition`, the backfill
{lit}`UPDATE t SET name = value`, then one CREATE TRIGGER statement for each trigger. The values bound to
each statement and the trigger names and definitions are arbitrary. -/
def migration (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value)) : Script :=
  ⟨derivedColumnScript tableName definition value addValues updateValues triggers⟩

/-- For every migration, none of its statements is written as INSERT from a query. Plain words: each
statement of a migration has one execution. Proof sketch: the statements are an ADD COLUMN, an UPDATE and
CREATE TRIGGER statements. -/
theorem migration_noInsertSelect (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) (addValues updateValues : List Value)
    (triggers : List ((Identifier × CatalogTrigger) × List Value)) :
    ∀ entry ∈ (migration tableName definition value addValues updateValues triggers).statements,
      entry.1.isInsertSelect = false := by
  intro entry member
  simp only [migration, derivedColumnScript, List.mem_cons, List.mem_map] at member
  rcases member with rfl | rfl | ⟨trigger, -, rfl⟩ <;> rfl

/-- A database has a table that the migration can extend: the table is physical, found by name at a
catalog position, and the column definition has no constraint, is admitted by the table, and names no
existing column. The written value resolves, in the scope of the table with the added column, to an
expression of the old columns that is context-free after assignment. The primary-key positions lie
inside the columns, the columns are plain (not generated), and the catalog with the new column added selects
no trigger for an UPDATE of that column. Other tables, indexes, triggers and rows are unrestricted. -/
structure Site (database : Database.Raw) (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) where
  /-- The catalog position of the table. -/
  position : Nat
  /-- The table with its rows. -/
  table : Table
  /-- The resolved written value, in the scope of the table with the added column. -/
  derived : Resolved.Expr
  /-- The comparison affinity that the resolution gives the written value. -/
  affinity : Option Affinity
  /-- The catalog finds the table by name at the position. -/
  found : database.catalog.findTable tableName = some (position, table.shape)
  /-- The database has this table at the position. -/
  present : database.table position = some table
  /-- The column definition has no constraint. -/
  constraintFree : definition.constraints = []
  /-- The table admits the declared type of the column. -/
  admitted : addColumnRestriction table.shape definition = none
  /-- No column has the name of the new column. -/
  fresh : columnPosition table.shape.columns definition.name = none
  /-- The written value resolves to the expression. -/
  operand : resolveOperand runContext.profile.dqsDml
    (backfillScope position tableName table.shape (definedColumn table.shape.strict definition)) {} true value =
      .ok (derived, affinity)
  /-- The expression reads only the old columns. -/
  below : derived.readsBelow table.shape.columns.length = true
  /-- The stored expression has the same value in every evaluation context. -/
  contextFree : (assignedExpression
    (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
    table.shape.columns.length value derived).ContextFree
  /-- Every primary-key position is a column of the table. -/
  keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length
  /-- No original column is generated. -/
  plain : ∀ old ∈ table.shape.columns, old.generated = none
  /-- With the new column added, the catalog selects no trigger for an UPDATE of that column. -/
  noneFiring : (database.catalog.addColumn position (definedColumn table.shape.strict definition)).triggersFiring
    { table := position, event := .update (some [table.shape.columns.length]) } = []

/-- The column that the migration adds at the site: the column of the definition, with the strictness of
the table. -/
def Site.column {database : Database.Raw} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} (site : Site database tableName definition value) : CatalogColumn :=
  definedColumn site.table.shape.strict definition

/-- The expression that the backfill assigns at the site, as the resolver forms it from the written
value. -/
def Site.assigned {database : Database.Raw} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} (site : Site database tableName definition value) : Resolved.Expr :=
  assignedExpression (backfillScope site.position tableName site.table.shape site.column)
    site.table.shape.columns.length value site.derived

/-- The database that the migration reaches at the site when it registers the given triggers in order:
{name}`Model.Database.addDerivedColumn`. -/
def Site.reached {database : Database.Raw} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} (site : Site database tableName definition value)
    (triggers : List (Identifier × CatalogTrigger)) : Database.Raw :=
  database.addDerivedColumn site.position site.table site.column site.assigned triggers

/-- For every site and list of triggers, with the position of the site inside the rows of the database, the
database {name}`Site.reached` stores as many rows in the table as the database. In plain words: the migration
adds no row and removes none. Proof sketch: {name}`Model.Database.rows_length_addDerivedColumn`. -/
theorem Site.reached_rows_length {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (site : Site database tableName definition value)
    (triggers : List (Identifier × CatalogTrigger)) (aligned : site.position < database.rows.length) :
    ((site.reached triggers).rows.getD site.position []).length = (database.rows.getD site.position []).length :=
  Model.Database.rows_length_addDerivedColumn site.column site.assigned triggers site.found site.present aligned

/-- For every site, migration values, connection whose database is the site's database, with wide aliased
rows in the site's table and both settings off, and a run of the migration script with only modeled,
error-free outputs: the run reaches the start connection with the database {name}`Site.reached` and some
counters, and it has one output for each trigger and two more. In plain words, a migration that succeeds
leaves exactly the database of the site. Clock, snapshot and settings stay. Proof sketch:
{name}`Model.derivedColumn_state` with the facts of the site. -/
theorem Site.run_state {database : Database.Raw} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} (site : Site database tableName definition value) (addValues updateValues : List Value)
    (triggers : List ((Identifier × CatalogTrigger) × List Value)) {clock : Option Clock} {index : Nat}
    {connection : Connection} (same : connection.state.database = database)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased)
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (ok : (runScriptFrom runContext clock index connection
      (derivedColumnScript tableName definition value addValues updateValues triggers)).outputs.all
        (fun output => !output.isError && !output.endsRun) = true) :
    ∃ counters,
      (runScriptFrom runContext clock index connection
        (derivedColumnScript tableName definition value addValues updateValues triggers)).connection =
        { connection with state := { connection.state with
          database := site.reached (triggers.map (·.1)), counters } } ∧
      (runScriptFrom runContext clock index connection
        (derivedColumnScript tableName definition value addValues updateValues triggers)).outputs.length =
          triggers.length + 2 := by
  subst same
  exact derivedColumn_state (context := runContext) (clock := clock) (index := index) (connection := connection)
    (tableName := tableName) (definition := definition) (value := value) site.table addValues updateValues triggers
    site.found site.present site.constraintFree site.admitted site.fresh site.operand site.below site.contextFree
    wide aliased site.plain foreign recursive site.noneFiring ok

/-- For every site, migration values, connection whose database is the site's database, with wide aliased
rows in the site's table and both settings off, a migration that succeeds from the connection, and every
branch of the migration, whatever its raw or concrete choices: the branch ends at a connection whose
database is {name}`Site.reached`. In plain words, a successful migration leaves exactly the database of the
site on every branch, and the counters can be anything. Proof sketch: {name}`Site.run_state` gives the model
run; every branch reaches the same connection ({name}`sendStatements_branch_shape`). -/
theorem Site.branch_database {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (site : Site database tableName definition value)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value))
    {clock : Option Clock} {index : Nat} {connection : Connection} (same : connection.state.database = database)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased)
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (success : (send (migration tableName definition value addValues updateValues triggers)).SucceedsFrom
      clock index connection)
    (run : SqlRun (List Output))
    (branch : (send (migration tableName definition value addValues updateValues triggers)).Branch
      clock index connection run) :
    run.connection.state.database = site.reached (triggers.map (·.1)) := by
  have ok : List.allOk (runScriptFrom runContext clock index connection
      (derivedColumnScript tableName definition value addValues updateValues triggers)).outputs = true :=
    Sql.allOk_of_succeedsFrom_send _ _ _ _ success
  obtain ⟨counters, reached, -⟩ := site.run_state addValues updateValues triggers same wide aliased foreign recursive ok
  obtain ⟨uniform, -⟩ := sendStatements_branch_shape _ _ _ _ run
    (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _
      (migration_noInsertSelect _ _ _ _ _ _)) branch
  rw [uniform]
  change (runScriptFrom runContext clock index connection
    (derivedColumnScript tableName definition value addValues updateValues triggers)).connection.state.database = _
  rw [reached]

end Belay.Sqlite.DerivedColumnMigration
