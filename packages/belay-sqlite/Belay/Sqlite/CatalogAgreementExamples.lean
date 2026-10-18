import Belay.Sqlite.CatalogAgreementLaws
import Belay.Sqlite.Resolution.Examples

set_option doc.verso true

/-! Checked uses of {name}`Belay.Sqlite.runSqlAt_catalog`: a script that creates a table,
adds a column and runs a transaction ends, when it has no error, with the catalog that
resolution predicts, for every starting database with the starting catalog. -/

namespace Belay.Sqlite.CatalogAgreementExamples

open Belay.Sqlite Resolution.Examples

/-- {lit}`CREATE TABLE u(a); BEGIN; ALTER TABLE u ADD COLUMN b; COMMIT; INSERT INTO u VALUES (1, 2);`. -/
def script : List Syntax.Statement :=
  [.createTable "u" [column "a"] [], .begin, .addColumn "u" (column "b"), .commit,
   .insert "u" none [[.numeric "1", .numeric "2"]] []]

/-- The resolution of {name}`script` from the empty catalog. -/
def resolution : ResolveResult := migration [] script

-- Resolution gives five statements and one table with two columns.
#guard (statements resolution).length == 5
#guard ((catalogOf resolution).columnsOf "u").map (·.map (·.name)) == some ["a", "b"]

/-- The resolution of {name}`script` succeeds with its statements and catalog. The kernel
computes it. -/
theorem resolved : resolve { profile := defaults, mode := .execution } [] script =
    .resolved (statements resolution) (catalogOf resolution) := by
  decide +kernel

/-- For every database with the empty catalog and every clock assignment, a run of the
resolved script without an error ends with the catalog that resolution predicts. -/
example (database : Database) (empty : database.catalog = []) (clock : Clock)
    (clean : (runSqlAt clock (statements resolution) database).error? = none) :
    (runSqlAt clock (statements resolution) database).database.catalog = catalogOf resolution :=
  runSqlAt_catalog clock resolved empty clean

-- The empty database runs the script without an error, so the theorem applies to it.
#guard (runSqlAt (fun _ => 0) (statements resolution) {}).error? == none
#guard (runSqlAt (fun _ => 0) (statements resolution) {}).database.catalog == catalogOf resolution

end Belay.Sqlite.CatalogAgreementExamples
