import Belay.Sqlite.Programs.Reasoning.MigrationPatternAfter
import Belay.Sqlite.Programs.Reasoning.SendStatementsBranches
import Belay.Sqlite.Programs.Claims.SingleStatementObservations
import Belay.Sqlite.Programs.Scripts.ScriptSuccess
import Belay.Sqlite.Schema.Columns.DerivedColumnMigration

set_option doc.verso true

/-! A migration that adds a column, backfills it from an expression and registers triggers (ADR 0017,
S6), as a migration pattern. A read that returns old columns keeps its result when its filter moves from
the expression to the stored column, as long as the two filters keep the same rows of the migrated table;
a read that does not read the new column is preserved. The theorems quantify over the table, the column
definition, the written expression, the triggers and the statements of the reads. The guide's lowercase
expansion is one instance. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

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
