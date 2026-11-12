import Belay.Sqlite.Model.Schema.Dispatch.Examples

set_option doc.verso true

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

end Belay.Sqlite.Model.CatalogAgreementExamples
