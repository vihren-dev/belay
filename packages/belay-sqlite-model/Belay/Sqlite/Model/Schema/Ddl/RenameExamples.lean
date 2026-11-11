import Belay.Sqlite.Model.Schema.Dispatch.Examples
import Belay.Sqlite.Model.Schema.Dispatch.Execution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.RenameExamples

open Belay.Sqlite.Model Syntax Belay.Sqlite.Model.Resolution.Examples

/-- The schema of the examples: the table {lit}`t(a, b)`, the index {lit}`ti` on {lit}`a`, the table
{lit}`u(x)`, the table {lit}`k(p, q)` with a primary key and a UNIQUE constraint, and the view {lit}`v` of {lit}`SELECT a FROM t`. -/
def objects : Catalog := catalogOf (schema [
  .createTable (name! "t") [column (name! "a"), column (name! "b")] [],
  .createIndex (name! "ti") false (name! "t") [key (name! "a")] none,
  .createTable (name! "u") [column (name! "x")] [],
  .createTable (name! "k") [column (name! "p"), column (name! "q")]
    [.primaryKey [name! "p"], .unique [name! "q"]],
  .createView (name! "v") false none
    { columns := [.expression (.identifier (name! "a") .none) none "a"], source := some { table := name! "t", alias := none },
      joins := [], filter := none, groupBy := [], orderBy := [], limit := none, offset := none, parent := none }])

/-- Whether the statement resolves to the rewrite of the catalog, and the rewrite runs on the empty database of
{name}`objects`: the run succeeds with the catalog that the resolution gives, and no row changes. -/
def rewritesAndRuns (statement : Syntax.Statement) : Bool :=
  let result := migration objects [statement]
  match statements result with
  | [resolved@(.rewrite renamed)] =>
    match step 0 {} [] resolved objects.emptyDatabase with
    | .ok database => renamed == catalogOf result && database.catalog == renamed && database.rows == objects.emptyDatabase.rows
    | .error _ => false
  | _ => false

/-- A rewrite whose catalog differs in outline from the catalog of the database (here the empty catalog) is
rejected: the run fails as {name}`ExecutionError.unmodeled` and returns the input database unchanged. -/
def rejectedRewriteKeepsDatabase : Bool :=
  match step 0 {} [] (.rewrite []) objects.emptyDatabase with
  | .error (.unmodeled, database) => database == objects.emptyDatabase
  | _ => false

#guard rejectedRewriteKeepsDatabase

-- A rename that passes every check is the rewrite of the catalog, and it runs.
#guard rewritesAndRuns (.renameTable (name! "t") (name! "w"))
#guard rewritesAndRuns (.renameTable (name! "t") (name! "w w"))

#guard rewritesAndRuns (.renameColumn (name! "t") (name! "A") (name! "c") "A" false)
-- SQLite renames a column to {lit}`rowid`; a column of that name is outside the model, so the rewrite is a restriction.
#guard restricted (migration objects [.renameColumn (name! "t") (name! "b") (name! "rowid") "b" false])

end Belay.Sqlite.Model.Resolution.RenameExamples
