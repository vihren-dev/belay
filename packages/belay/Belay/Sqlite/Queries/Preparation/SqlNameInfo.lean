import Belay.Sqlite.Queries.Preparation.SqlNameCorrections
import Belay.Sqlite.Queries.Preparation.SqlNameDescription
import Belay.Sqlite.Frontend.Embedding.SqlNameInfo

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Meta Belay.Sqlite.Model

/-- The warning for a double-quoted name that the resolver reads as a text literal. It states that
interpretation and does not claim anything about the statement that uses the literal. -/
def doubleQuoteWarning (written : String) (name : Identifier) : String :=
  s!"No column in scope has the name {written}, so SQLite reads it as the text literal '{name}'. " ++
    "Write the text in single quotes, or write the name of a column in scope"

/-- The written text of a range of the SQL bytes. -/
def writtenText (bytes : ByteArray) (site : NameSite) : String :=
  (String.fromUTF8? (bytes.extract site.start site.stop)).getD ""

/-- Emit the information of an unknown name of a place: the warning of the double-quote fallback at
the occurrence, and the corrections at the exactly mapped identifier. A correction that the literal
cannot take ({name}`SqlEditorSource.accepts`), such as a quoted name in a raw literal without
{lit}`#`, is not offered; the list is all or nothing, so a tie never hides an option. -/
def emitUnknownName (source : SqlEditorSource) (file : FileMap) (bytes : ByteArray) (site : NameSite)
    (name : Identifier) (use : MissingUse) (candidates : List Candidate) : TermElabM Unit := do
  let written := writtenText bytes site
  if use matches .textLiteral then
    if let some ref := source.warningRef? file site.start site.stop then
      logWarningAt ref (doubleQuoteWarning written name)
  let tokens := correctionTokens written name candidates
  if tokens.all (source.accepts site.start site.stop) then
    if let some identifier := source.identifier? file site.start site.stop Name.anonymous then
      suggestCorrections identifier written tokens

/-- The columns that the resolver found for a column name, or none for any other occurrence. A name
that is ambiguous has no found column, so the editor describes none. -/
def foundColumns? (occurrence : NameOccurrence) : Option (List Binding) :=
  match occurrence.result with
  | .found bindings =>
    match occurrence.role with
    | .columnReference | .columnTarget => if bindings.isEmpty then none else some bindings
    | .tableReference | .qualifier | .aliasDeclaration | .resultAlias | .comparisonSite => none
  | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares | .compared ..
  | .unreached _ => none

end Belay.Sqlite
