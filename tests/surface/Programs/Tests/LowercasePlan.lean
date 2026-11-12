import LowercaseQueries

set_option doc.verso true

/-! The lowercase-field expansion as one plan, and the lookups across it as a scoped simulation (ADR 0017,
S8). The interface has one call: the lookup of an id by a value. Its old entry reads {lit}`WHERE
lower(source) = lower(?1)` and its new entry reads {lit}`WHERE stored = lower(?1)`. The relation between an
old context and a new context names the clock, the facts of the old connection, and the migrated database of
the new connection. It names no counter, no statement index and no output trace. The relation holds at the
migrated context of every successful expansion, and each lookup keeps it. The lookup theorem therefore
covers every application over this interface, including one that chooses its later lookups from earlier
results, on every database with a site. A write, a counter read or a change of the connection outside the
relation is outside this theorem. The general laws come from {lit}`DerivedColumnMigration` and the model;
this module only fixes the expression to {lit}`lower`. -/

namespace LowercaseFixture
open Belay.Sqlite Belay.Sqlite.Calls
open Belay.Sqlite.Model hiding Database Output

/-- The names, the two triggers and the bound values of one lowercase-field expansion of a table: the table
with an optional alias, the id column, the source column, the new stored column, the text and the number of
the parameter of the lookups, and the four statements' values. -/
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

/-- The facts about a connection that the expansion of a plan needs: a {name}`LowercaseSite` for the
database of the connection, wide and aliased rows in its table, a position of the table inside the list of
rows, and both foreign keys and recursive triggers off. Other tables, indexes, triggers and rows are
unrestricted. -/
structure Plan.Source (plan : Plan) (connection : Connection) where
  /-- The site of the table, as for the expansion laws. -/
  site : LowercaseSite connection.state.database plan.tableName plan.idName plan.sourceName plan.storedName
  /-- Every row of the table has one cell for each column. -/
  wide : site.table.RowsWide
  /-- Every row of the table is aliased ({name}`Table.RowsAliased`): if the table has a rowid alias, the
  alias cell of each row agrees with the rowid of the row. -/
  aliased : site.table.RowsAliased
  /-- The position of the table is inside the list of rows. -/
  aligned : site.position < connection.state.database.rows.length
  /-- Foreign key enforcement is off. -/
  foreignKeys : connection.foreignKeys = false
  /-- Recursive triggers are off. -/
  recursiveTriggers : connection.recursiveTriggers = false

/-- The expansion facts of a valid database that has a site, on its connection with any counters. The rows
of a valid database are wide and aliased, and its list of rows matches its tables. Both settings are off on
a new connection. -/
def Plan.Source.ofDatabase (plan : Plan) (db : Database) (counters : Counters)
    (site : LowercaseSite db.raw plan.tableName plan.idName plan.sourceName plan.storedName) :
    plan.Source (db.raw.connection counters) where
  site := site
  wide := db.valid.admitted.rowsWide site.position site.table site.present
  aliased := db.valid.admitted.rowsAliased site.position site.table site.present
  aligned := by
    show site.position < db.raw.rows.length
    rw [db.valid.admitted.rowsShaped.1]; exact Belay.Sqlite.Model.Database.table_lt site.present
  foreignKeys := rfl
  recursiveTriggers := rfl

/-- The database that the expansion reaches from the database of the connection. -/
def Plan.Source.expanded {plan : Plan} {connection : Connection} (source : plan.Source connection) :
    Database.Raw :=
  source.site.toSite.reached [plan.first, plan.second]

/-- For every plan, connection with the expansion facts, clock and index: if the expansion succeeds from
that connection, then every branch of the expansion, whatever its raw or concrete choices, ends at a
connection whose database is the expanded database. Plain words: a successful expansion leaves exactly the
expanded database, and the counters can be anything. Proof sketch: the general
{lit}`DerivedColumnMigration.Site.branch_database`. -/
theorem Plan.Source.after_expansion {plan : Plan} {clock : Option Clock} {index : Nat} {connection : Connection}
    (source : plan.Source connection) (success : plan.migration.SucceedsFrom clock index connection)
    (run : SqlRun (List Output)) (branch : plan.migration.Branch clock index connection run) :
    run.connection.state.database = source.expanded :=
  source.site.toSite.branch_database plan.firstValues plan.secondValues
    [(plan.first, plan.thirdValues), (plan.second, plan.fourthValues)] rfl source.wide source.aliased
    source.foreignKeys source.recursiveTriggers success run branch

end LowercaseFixture
