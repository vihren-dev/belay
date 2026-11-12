import Belay.Sqlite.Model.Queries.Preparation.InsertSelectKeeps
import Belay.Sqlite.Model.Schema.Rows.DatabaseFacts
import Belay.Sqlite.Model.Shared.Resolved.StatementCatalog

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For the given limits and database: the catalog is valid under the limits ({name}`Catalog.Valid`). It is the
atom "catalog supported" of {name}`Database.Admitted`, with the limits of the profile. -/
abbrev Database.CatalogSupported (limits : Limits) (database : Database) : Prop := database.catalog.Valid limits

/-- For the given database: the rows are stored ({name}`Database.RowsStored`) and wide
({name}`Database.RowsWide`). It is the invariant of the run theorem of "rows stored", which lists "rows wide". -/
abbrev Database.RowsStoredWide (database : Database) : Prop := database.RowsStored ∧ database.RowsWide

/-- For the given limits and database: the rows are aliased ({name}`Database.RowsAliased`) and the catalog is valid
under the limits ({name}`Database.CatalogSupported`). It is the invariant of the run theorem of "rows aliased", which
lists "catalog supported". -/
abbrev Database.RowsAliasedSupported (limits : Limits) (database : Database) : Prop :=
  database.RowsAliased ∧ database.CatalogSupported limits

/-- The condition of "catalog supported" for a statement on a database and limits: the catalog after the
statement ({name}`Resolved.Statement.applyCatalog`) is valid under the limits. Statements that
leave the catalog unchanged require validity of the input catalog. -/
abbrev Resolved.Statement.AppliedValid (limits : Limits) (statement : Resolved.Statement) (database : Database) : Prop :=
  (statement.applyCatalog database.catalog).Valid limits

end Belay.Sqlite.Model
