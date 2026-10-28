import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.AdmittedCatalogStatement
import Belay.Sqlite.Model.AdmittedDistinctStatement
import Belay.Sqlite.Model.AdmittedRangeWideStatements
import Belay.Sqlite.Model.AdmittedShapedStatement
import Belay.Sqlite.Model.AdmittedStoredAliasedStatements
import Belay.Sqlite.Model.RunHolds

set_option doc.verso true

/-! Independent preservation certificates for the admitted atoms. Catalog validity, row shape
and distinct rowids need no readiness premise. Range, width, stored form and row aliases use
the raw statement readiness condition. The combined certificate preserves all seven fields. -/

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

/-- For every limits and evaluator inputs, a database with a valid catalog and a valid applied
catalog keeps catalog validity on every effect in {name}`StatementKeeps`, without readiness. Proof sketch: lift {name}`runStatement_catalogSupported` to all effects. -/
theorem catalogSupported_statementKeeps (limits : Limits) :
    StatementKeeps (Database.CatalogSupported limits) (fun _ _ _ => Resolved.Statement.AppliedValid limits) :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ valid applied =>
    runStatement_catalogSupported limits clock counters parameters statement valid applied)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

/-- For every evaluator input, a database with shaped rows keeps that property on every effect
in {name}`StatementKeeps`, independently of readiness and other atoms.
Proof sketch: lift {name}`runStatement_rowsShaped` to all effects. -/
theorem rowsShaped_statementKeeps : StatementKeeps Database.RowsShaped fun _ _ _ _ _ => True :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ shaped _ =>
    runStatement_rowsShaped clock counters parameters statement shaped)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

/-- For every evaluator input, a database with distinct rowids keeps that property on every
effect in {name}`StatementKeeps`, independently of readiness and other atoms.
Proof sketch: lift {name}`runStatement_rowidsDistinct` to all effects. -/
theorem rowidsDistinct_statementKeeps : StatementKeeps Database.RowidsDistinct fun _ _ _ _ _ => True :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ distinct _ =>
    runStatement_rowidsDistinct clock counters parameters statement distinct)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

/-- For every evaluator input, a database with rowids in range keeps that property on every
effect in {name}`StatementKeeps` when the raw statement run is ready. Proof sketch: lift {name}`runStatement_rowidsInRange`, transporting readiness to each selected upsert. -/
theorem rowidsInRange_statementKeeps :
    StatementKeeps Database.RowidsInRange fun clock counters parameters statement database =>
      (runStatement clock counters parameters statement database).ready = true :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ inRange ready =>
    runStatement_rowidsInRange clock counters parameters statement inRange ready)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ ready met => ready met)

/-- For every evaluator input, a database with wide rows keeps that property on every effect
in {name}`StatementKeeps` when the raw statement run is ready.
Proof sketch: lift {name}`runStatement_rowsWide`, transporting readiness to each selected upsert. -/
theorem rowsWide_statementKeeps :
    StatementKeeps Database.RowsWide fun clock counters parameters statement database =>
      (runStatement clock counters parameters statement database).ready = true :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ wide ready =>
    runStatement_rowsWide clock counters parameters statement wide ready)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ ready met => ready met)

/-- For every evaluator input, a database with stored and wide rows keeps both properties on
every effect in {name}`StatementKeeps` when the raw statement run is ready.
Proof sketch: combine the two independent statement facts and transport readiness to selected upserts. -/
theorem rowsStored_statementKeeps :
    StatementKeeps Database.RowsStoredWide fun clock counters parameters statement database =>
      (runStatement clock counters parameters statement database).ready = true :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds ready database kept =>
    ⟨runStatement_rowsStored clock counters parameters statement holds.1 holds.2 ready database kept,
      runStatement_rowsWide clock counters parameters statement holds.2 ready database kept⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ ready met => ready met)

/-- For every limits and evaluator inputs, a database with aliased rows and a valid catalog
keeps both properties on every effect in {name}`StatementKeeps` when the applied catalog is
valid and the raw statement run is ready. Proof sketch: combine the row-alias and catalog facts;
the INSERT-query bridge transports readiness to selected upserts. -/
theorem rowsAliased_statementKeeps (limits : Limits) :
    StatementKeeps (Database.RowsAliasedSupported limits) fun clock counters parameters statement database =>
      statement.AppliedValid limits database ∧ (runStatement clock counters parameters statement database).ready = true :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ holds met database kept =>
    ⟨runStatement_rowsAliased limits clock counters parameters statement holds.1 holds.2 met.2 database kept,
      runStatement_catalogSupported limits clock counters parameters statement holds.2 met.1 database kept⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ ready met => ⟨met.1, ready met.2⟩)

/-- For every profile and evaluator inputs, an admitted database stays admitted on every effect
in {name}`StatementKeeps` when the applied catalog is valid and the raw statement run is ready. Proof sketch: prove the seven fields independently, then lift to
all effects using the INSERT-query readiness implication. -/
theorem admitted_statementKeeps (profile : Profile) :
    StatementKeeps (Database.Admitted profile) fun clock counters parameters statement database =>
      statement.AppliedValid profile.limits database ∧ (runStatement clock counters parameters statement database).ready = true :=
  StatementKeeps.ofOwnRun (fun clock counters parameters statement _ admitted met database kept =>
    ⟨runStatement_catalogSupported profile.limits clock counters parameters statement admitted.catalogSupported
        met.1 database kept,
      runStatement_rowsShaped clock counters parameters statement admitted.rowsShaped database kept,
      runStatement_rowidsDistinct clock counters parameters statement admitted.rowidsDistinct database kept,
      runStatement_rowidsInRange clock counters parameters statement admitted.rowidsInRange met.2 database kept,
      runStatement_rowsWide clock counters parameters statement admitted.rowsWide met.2 database kept,
      runStatement_rowsStored clock counters parameters statement admitted.rowsStored admitted.rowsWide met.2
        database kept,
      runStatement_rowsAliased profile.limits clock counters parameters statement admitted.rowsAliased
        admitted.catalogSupported met.2 database kept⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ ready met => ⟨met.1, ready met.2⟩)

end Belay.Sqlite.Model
