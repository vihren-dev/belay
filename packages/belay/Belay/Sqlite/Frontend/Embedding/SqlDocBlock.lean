import Belay.Sqlite.Frontend.Embedding.SqlDocBindings
import Belay.Sqlite.Frontend.Embedding.SqlDocComments
import Belay.Sqlite.Frontend.Embedding.SqlDocFailure
import Belay.Sqlite.Frontend.Embedding.SqlDocInputs
import Belay.Sqlite.Frontend.Embedding.SqlTerm

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Belay.Sqlite

/-- The syntax where a problem is shown. -/
def problemReference (header : Header) : Place → Option Syntax
  | .sql _ _ => none
  | .header "values" => header.explicitValues.map (·.reference)
  | .header name => (header.bindings.find? (·.name == name)).map (·.reference)

/-- Log each problem at its SQL token or its header argument. -/
def reportProblems (source : BlockSource) (header : Header) (problems : List Problem) : TermElabM Unit :=
  for problem in problems do
    match problem.place with
    | .sql start stop => source.reportSql start stop problem.message
    | place => logErrorAt ((problemReference header place).getD source.block) problem.message

/-- The message when an expected failure compares to a different one. -/
def errorMismatch (expected actual : String) : String :=
  s!"SQL error mismatch\nexpected message: {repr expected}\nactual message: {repr actual}\n\
    Correct the SQL, or write the actual message in the comment lines at the end of the block"

end Belay.Sqlite.SqlDoc
