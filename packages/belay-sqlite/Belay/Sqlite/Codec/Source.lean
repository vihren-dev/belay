import Belay.Sqlite.Codec.Resolution

set_option doc.verso true

/-! Lean source of the generated input modules. Each value is a literal term: the
derived {lit}`Repr` of the value, which names every constructor in full. The gates
do not trust this text. They compute the values again and compare them with the
compiled declarations, so a wrong term rejects the request. -/

namespace Belay.Sqlite

/-- A value as Lean source text, on its own lines with every line indented by two
spaces. A structure instance that spans lines needs its fields at or after the
column of its brace, so the term starts at the beginning of a line. -/
def leanTerm [Repr α] (value : α) : String :=
  "\n" ++ "\n".intercalate (((repr value).pretty.splitOn "\n").map ("  " ++ ·))

/-- The module {lit}`SchemaInputs`: the profile, the schema statements and the
starting catalog. The approved files import it. -/
def schemaInputsSource (request : ResolvedRequest) : String :=
  "import SqliteVerifier\n\nnamespace Generated\nopen Belay.Sqlite\n\n" ++
  s!"def profile : Profile :={leanTerm request.profile}\n\n" ++
  s!"def schema : List Syntax.Statement :={leanTerm request.schema}\n\n" ++
  s!"def startCatalog : Catalog :={leanTerm request.startCatalog}\n\nend Generated\n"

/-- The module {lit}`SqlInputs`: the migration statements, the resolved statements
and the resulting catalog. -/
def sqlInputsSource (request : ResolvedRequest) : String :=
  "import SchemaInputs\n\nnamespace Generated\nopen Belay.Sqlite\n\n" ++
  s!"def script : List Syntax.Statement :={leanTerm request.script}\n\n" ++
  s!"def resolved : List Resolved.Statement :={leanTerm request.resolved}\n\n" ++
  s!"def nextCatalog : Catalog :={leanTerm request.nextCatalog}\n\nend Generated\n"

end Belay.Sqlite
