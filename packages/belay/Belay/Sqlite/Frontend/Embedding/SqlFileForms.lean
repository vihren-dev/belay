import Belay.Sqlite.Frontend.Embedding.SqlFileLoad
import Belay.Sqlite.Frontend.Embedding.SqlFileTerm

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- A file read and translated at a form: its source, its statements with their ranges and
parameters, and the markers found among them. -/
structure LoadedSqlFile where
  /-- The file as read from its package. -/
  source : SqlFileSource
  /-- The translated statements, with ranges in the whole file. -/
  statements : Array Translation.ParameterizedStatement
  /-- The statement ranges and markers. -/
  layout : FileStructure

/-- Read and translate the package-relative file. A file the parser rejects is an error at the
form that names the SQL position. -/
def loadSqlFile (reference : Syntax) (path : String) : TermElabM LoadedSqlFile := do
  let source ← loadSqlFileSource reference path
  let statements ← match ← (translateText source.text : IO _) with
    | .ok statements => pure statements
    | .error error =>
      let hint := (toolSyntaxHint source.text.toUTF8 error.start).elim "" ("; " ++ ·)
      throwErrorAt reference (source.diagnostic ⟨error.start, error.stop, error.message ++ hint⟩)
  let ranges := statements.map fun item => (item.statement.span.start, item.statement.span.stop)
  return { source, statements, layout := FileStructure.ofRanges source.text.toUTF8 ranges }

/-- Raise a selection problem at the form, naming the SQL position and the entry. -/
def LoadedSqlFile.fail {α : Type} (file : LoadedSqlFile) (reference : Syntax) (problem : FileProblem)
    (entry : Option String := none) : TermElabM α :=
  throwErrorAt reference (file.source.problem problem entry)

/-- The chosen statements, in file order. -/
def LoadedSqlFile.chosen (file : LoadedSqlFile) (selection : FileSelection) :
    Array Translation.ParameterizedStatement :=
  selection.statements.filterMap fun index => file.statements[index]?

/-- The text of the file that contains exactly the selected statements. -/
def LoadedSqlFile.replayText (file : LoadedSqlFile) (selection : FileSelection) : String :=
  (String.fromUTF8? (file.source.text.toUTF8.extract selection.replayStart selection.replayStop)).getD ""

end Belay.Sqlite
