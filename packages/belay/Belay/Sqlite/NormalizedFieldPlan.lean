import Belay.Sqlite.NormalizedFieldExpansion
import Belay.Sqlite.MigrationPatternSuccess

set_option doc.verso true

/-! The lowercase-field expansion as one plan (ADR 0017, S8). The expansion laws of
{lit}`NormalizedFieldExpansion` take the table, the column names, the two triggers and the values bound to
the four statements as separate arguments. A {lit}`Plan` collects
them, so a migration, an interface and a relation can share one value. A connection that the plan
applies to carries the facts of a {name}`Belay.Sqlite.NormalizedFieldExpansion.Site` and the row facts
of its database. After a successful run of the expansion, every branch reaches the expanded database. -/

namespace Belay.Sqlite.NormalizedFieldExpansion
open Belay.Sqlite.Model Belay.Sqlite.Model.NormalizedField

/-- The names, the two triggers and the bound values of one lowercase-field expansion of a table:
the table with an optional alias, the id column, the source column, the new stored column, the text and
the number of the parameter of the lookups, and the four statements' values. -/
structure Plan where
  /-- The table that gains the stored column. -/
  tableName : Identifier
  /-- The alias that the lookups give the table, if any. -/
  alias : Option Identifier
  /-- The id column that the lookups return. -/
  idName : Identifier
  /-- The column whose lowercase the stored column keeps. -/
  sourceName : Identifier
  /-- The new stored column. -/
  storedName : Identifier
  /-- The text of the result column of the lookups. -/
  text : String
  /-- The number of the parameter of the lookups. -/
  number : Nat
  /-- The trigger that fills the stored column after an INSERT. -/
  first : Identifier × CatalogTrigger
  /-- The trigger that fills the stored column after an UPDATE of the source column. -/
  second : Identifier × CatalogTrigger
  /-- The values bound to the ALTER TABLE statement. -/
  firstValues : List Value
  /-- The values bound to the backfill UPDATE statement. -/
  secondValues : List Value
  /-- The values bound to the first CREATE TRIGGER statement. -/
  thirdValues : List Value
  /-- The values bound to the second CREATE TRIGGER statement. -/
  fourthValues : List Value

/-- The four-statement expansion of a plan, sent as a program. -/
def Plan.migration (plan : Plan) : Sql (List Output) :=
  send (expansion plan.tableName plan.storedName plan.sourceName plan.first plan.second plan.firstValues
    plan.secondValues plan.thirdValues plan.fourthValues)

/-- The facts about a connection that the expansion of a plan needs. They are: a {name}`Site` for the
database of the connection, wide and aliased rows in its table, a position of the table inside the list of
rows, and both foreign keys and recursive triggers off. Other tables, indexes, triggers and rows are
unrestricted. -/
structure Plan.Source (plan : Plan) (connection : Connection) where
  /-- The site of the table, as for the expansion laws. -/
  site : Site connection.state.database plan.tableName plan.idName plan.sourceName plan.storedName
  /-- Every row of the table has one cell for each column. -/
  wide : site.table.RowsWide
  /-- Every row of the table is aliased: its rowid-alias cell agrees with its rowid. -/
  aliased : site.table.RowsAliased
  /-- The position of the table is inside the list of rows. -/
  aligned : site.position < connection.state.database.rows.length
  /-- Foreign key enforcement is off. -/
  foreignKeys : connection.foreignKeys = false
  /-- Recursive triggers are off. -/
  recursiveTriggers : connection.recursiveTriggers = false

/-- The expansion facts of a valid database that has a site, on its connection with any counters. The
rows of a valid database are wide and aliased, and its list of rows matches its tables. Both settings
are off on a new connection. -/
def Plan.Source.ofDatabase (plan : Plan) (db : Database) (counters : Counters)
    (site : Site db.raw plan.tableName plan.idName plan.sourceName plan.storedName) :
    plan.Source (db.raw.connection counters) where
  site := site
  wide := db.valid.admitted.rowsWide site.position site.table site.present
  aliased := db.valid.admitted.rowsAliased site.position site.table site.present
  aligned := by
    show site.position < db.raw.rows.length
    rw [db.valid.admitted.rowsShaped.1]; exact Database.table_lt site.present
  foreignKeys := rfl
  recursiveTriggers := rfl

/-- The database that the expansion reaches from the database of the connection. -/
def Plan.Source.expanded {plan : Plan} {connection : Connection} (source : plan.Source connection) :
    Database.Raw :=
  expandedDatabase connection.state.database source.site.position source.site.source source.site.table
    plan.storedName plan.first plan.second

/-- For every plan, connection with the expansion facts, clock and index: if the expansion succeeds from
that connection, then every branch of the expansion, whatever its raw or concrete choices, ends at a
connection whose database is the expanded database. Plain words: a successful expansion leaves exactly
the expanded database, and the counters can be anything. Proof sketch: success of the sent script gives
the model run; {name}`Model.NormalizedField.expansion_state` gives its connection; every branch reaches
the same connection ({name}`sendStatements_branch_shape`). -/
theorem Plan.Source.after_expansion {plan : Plan} {clock : Option Clock} {index : Nat} {connection : Connection}
    (source : plan.Source connection) (success : plan.migration.SucceedsFrom clock index connection)
    (run : SqlRun (List Output)) (branch : plan.migration.Branch clock index connection run) :
    run.connection.state.database = source.expanded := by
  have ok : List.allOk (runScriptFrom runContext clock index connection
      (Model.NormalizedField.expansionScript plan.tableName plan.storedName plan.sourceName plan.first plan.second
        plan.firstValues plan.secondValues plan.thirdValues plan.fourthValues)).outputs = true :=
    (Sql.succeedsFrom_sendStatements _ _ _ _).mp success
  obtain ⟨counters, hconn, -⟩ := expansion_state (context := runContext) (clock := clock) (index := index)
    (connection := connection) (tableName := plan.tableName) (name := plan.storedName)
    (sourceName := plan.sourceName) source.site.table plan.first plan.second plan.firstValues plan.secondValues
    plan.thirdValues plan.fourthValues source.site.found source.site.present source.site.fresh
    source.site.sourceFound source.wide source.aliased source.site.plain source.foreignKeys
    source.recursiveTriggers source.site.noneFiring ok
  obtain ⟨same, -⟩ := sendStatements_branch_shape _ _ _ _ run branch
  have same' : run.connection = (runScriptFrom runContext clock index connection
      (Model.NormalizedField.expansionScript plan.tableName plan.storedName plan.sourceName plan.first plan.second
        plan.firstValues plan.secondValues plan.thirdValues plan.fourthValues)).connection := same
  rw [same', hconn]
  rfl

end Belay.Sqlite.NormalizedFieldExpansion
