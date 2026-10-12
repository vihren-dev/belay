import Belay.Sqlite.Codec.Resolution

set_option doc.verso true

/-! Lean source of the generated input modules. Each value is a literal term: the
derived {lit}`Repr` of the value, which names every constructor in full. A reader
that must not trust this text computes the values itself and compares them with
the compiled declarations, so that a wrong term is found. -/

namespace Belay.Sqlite

/-- A value as Lean source text, on its own lines with every line indented by two
spaces. A structure instance that spans lines needs its fields at or after the
column of its brace, so the term starts at the beginning of a line. -/
def leanTerm [Repr α] (value : α) : String :=
  "\n" ++ "\n".intercalate (((repr value).pretty.splitOn "\n").map ("  " ++ ·))

/-- The module {lit}`SchemaInputs`, in namespace {lit}`Generated`: the profile, the
schema statements and the starting catalog. -/
def schemaInputsSource (resolution : ResolvedScript) : String :=
  "import SqliteVerifier\n\nnamespace Generated\nopen Belay.Sqlite\n\n" ++
  s!"def profile : Profile :={leanTerm resolution.profile}\n\n" ++
  s!"def schema : List Syntax.Statement :={leanTerm resolution.schema}\n\n" ++
  s!"def startCatalog : Catalog :={leanTerm resolution.startCatalog}\n\nend Generated\n"

/-- The module {lit}`SqlInputs`, in namespace {lit}`Generated`, which imports
{lit}`SchemaInputs`: the script statements, the resolved statements and the
resulting catalog. -/
def sqlInputsSource (resolution : ResolvedScript) : String :=
  "import SchemaInputs\n\nnamespace Generated\nopen Belay.Sqlite\n\n" ++
  s!"def script : List Syntax.Statement :={leanTerm resolution.script}\n\n" ++
  s!"def resolved : List Resolved.Statement :={leanTerm resolution.resolved}\n\n" ++
  s!"def nextCatalog : Catalog :={leanTerm resolution.nextCatalog}\n\nend Generated\n"

end Belay.Sqlite
