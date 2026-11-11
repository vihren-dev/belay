import Belay.Sqlite.Model.Programs.Claims.CatalogAgreementLaws
import Belay.Sqlite.Model.Schema.Dispatch.CatalogAgreementExamples

set_option doc.verso true

/-! Checked uses of {name}`Belay.Sqlite.Model.runSqlAt_catalog`: a script that creates a table,
adds a column and runs a transaction ends, when it has no error, with the catalog that
resolution predicts, for every starting database with the starting catalog. -/

namespace Belay.Sqlite.Model.CatalogAgreementExamples

open Belay.Sqlite.Model Resolution.Examples

/-- For every database with the empty catalog, every list of values of the statements and every
clock assignment, a run of the resolved script with the values without an error ends with the
catalog that resolution predicts. -/
example (database : Database) (empty : database.catalog = []) (clock : Clock) (values : List (List Value))
    (clean : (runSqlAt clock (bindValues (statements resolution) values) database).error? = none) :
    (runSqlAt clock (bindValues (statements resolution) values) database).database.catalog = catalogOf resolution :=
  runSqlAt_catalog clock resolved empty values clean

-- The empty database runs the script without an error, so the theorem applies to it.
#guard (runSqlAt (fun _ => 0) (bindValues (statements resolution) []) {}).error? == none
#guard (runSqlAt (fun _ => 0) (bindValues (statements resolution) []) {}).database.catalog == catalogOf resolution

end Belay.Sqlite.Model.CatalogAgreementExamples
