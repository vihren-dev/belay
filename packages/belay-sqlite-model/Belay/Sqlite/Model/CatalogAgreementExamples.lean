import Belay.Sqlite.Model.CatalogAgreementLaws
import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Checked uses of {name}`Belay.Sqlite.Model.runSqlAt_catalog`: a script that creates a table,
adds a column and runs a transaction ends, when it has no error, with the catalog that
resolution predicts, for every starting database with the starting catalog. -/

namespace Belay.Sqlite.Model.CatalogAgreementExamples

open Belay.Sqlite.Model Resolution.Examples

/-- {lit}`CREATE TABLE u(a); BEGIN; ALTER TABLE u ADD COLUMN b; COMMIT; INSERT INTO u VALUES (1, 2);`. -/
def script : List Syntax.Statement :=
  [.createTable (name! "u") [column (name! "a")] [], .begin, .addColumn (name! "u") (column (name! "b")), .commit,
   .insert (name! "u") none [[.numeric "1", .numeric "2"]] []]

/-- The resolution of {name}`script` from the empty catalog. -/
def resolution : ResolveResult := migration [] script

-- Resolution gives five statements and one table with two columns.
#guard (statements resolution).length == 5
#guard ((catalogOf resolution).columnsOf (name! "u")).map (·.map (·.name)) == some [name! "a", name! "b"]

/-- The resolution of {name}`script` succeeds with its statements and catalog. The kernel
computes it. -/
theorem resolved : resolve { profile := defaults, mode := .execution } [] script =
    .resolved (statements resolution) (catalogOf resolution) := by
  decide +kernel

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
