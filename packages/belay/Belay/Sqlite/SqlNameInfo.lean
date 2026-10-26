import Belay.Sqlite.SqlNameCorrections
import Belay.Sqlite.SqlNameDescription
import Belay.Sqlite.SqlEditorSource
import Lean.Elab.Term
import Lean.Meta.Tactic.TryThis

set_option doc.verso true

/-! The native editor information of the names that the name trace decided (the editor task,
part 2b): a hover and a semantic token for a column, a hover for a comparison, and, for a name that
no scope has, a warning for the double-quote fallback and the code actions that correct the name.
Lean derives semantic tokens from term information only for a local variable, so a column is
the local {lit}`variable` of the row, with the hover text of the resolver. The correction uses the
native "try this" mechanism, whose code action replaces exactly the range of the identifier. -/

namespace Belay.Sqlite

open Lean Elab Term Meta Belay.Sqlite.Model

/-- Attach a hover to the mapped range of a column. The term information is a local variable of the
type {name}`Belay.Sqlite.Model.Value`, so the server colors the token as a variable; the nested
information supplies the hover text. -/
def addSqlColumnInfo (identifier : Syntax) (description : String) : TermElabM Unit :=
  withLocalDeclD identifier.getId (Lean.mkConst ``Belay.Sqlite.Model.Value) fun row => do
    let term : TermInfo :=
      { stx := identifier, expr := row, lctx := ← getLCtx, elaborator := .anonymous, expectedType? := none }
    let detail : DelabTermInfo := { term with mkDocString? := some fun _ => pure description, explicit := false }
    pushInfoTree (.node (.ofTermInfo term) (({} : PersistentArray InfoTree).push (.node (.ofDelabTermInfo detail) {})))

/-- Attach a hover with no semantic token to the mapped range of an expression. -/
def addSqlHoverInfo (identifier : Syntax) (description : String) : TermElabM Unit := do
  let term : TermInfo :=
    { stx := identifier, expr := mkStrLit "", lctx := ← getLCtx, elaborator := .anonymous, expectedType? := none }
  let detail : DelabTermInfo := { term with mkDocString? := some fun _ => pure description, explicit := false }
  pushInfoTree (.node (.ofTermInfo term) (({} : PersistentArray InfoTree).push (.node (.ofDelabTermInfo detail) {})))

/-- The warning for a double-quoted name that the resolver reads as a text literal. It states that
interpretation and does not claim anything about the statement that uses the literal. -/
def doubleQuoteWarning (written : String) (name : Identifier) : String :=
  s!"No column in scope has the name {written}, so SQLite reads it as the text literal '{name}'. " ++
    "Write the text in single quotes, or write the name of a column in scope"

/-- Offer the replacement tokens at the identifier as code actions: one suggestion for the unique
nearest name, a list for a tie. Nothing is offered for the empty list. -/
def suggestCorrections (identifier : Syntax) (written : String) (tokens : List String) : TermElabM Unit := do
  let suggestion (token : String) : Lean.Meta.Tactic.TryThis.Suggestion :=
    { suggestion := .string token, toCodeActionTitle? := some fun text => s!"Replace {written} with {text}" }
  match tokens with
  | [] => pure ()
  | [only] => Lean.Meta.Tactic.TryThis.addSuggestion identifier (suggestion only) (header := "Nearest name in scope:")
  | several =>
    Lean.Meta.Tactic.TryThis.addSuggestions identifier (several.map suggestion).toArray
      (header := "Names in scope at the same distance:")

/-- The written text of a range of the SQL bytes. -/
def writtenText (bytes : ByteArray) (site : NameSite) : String :=
  (String.fromUTF8? (bytes.extract site.start site.stop)).getD ""

/-- Emit the information of an unknown name of a place: the warning of the double-quote fallback at
the occurrence, and the corrections at the exactly mapped identifier. -/
def emitUnknownName (source : SqlEditorSource) (file : FileMap) (bytes : ByteArray) (site : NameSite)
    (name : Identifier) (use : MissingUse) (candidates : List Candidate) : TermElabM Unit := do
  let written := writtenText bytes site
  if use matches .textLiteral then
    if let some ref := source.warningRef? file site.start site.stop then
      logWarningAt ref (doubleQuoteWarning written name)
  if let some identifier := source.identifier? file site.start site.stop Name.anonymous then
    suggestCorrections identifier written (correctionTokens written name candidates)

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

/-- Emit the editor information of one place: the hover of a found column, the hover of the
comparisons, and the warning and corrections of an unknown name. A name that is ambiguous gets no
hover, because no column is the one that the resolver chose. -/
def emitNameSite (source : SqlEditorSource) (file : FileMap) (bytes : ByteArray) (catalog : Catalog)
    (site : NameSite) : TermElabM Unit := do
  let comparison := comparisonDescription site.occurrences
  if !comparison.isEmpty then
    if let some identifier := source.identifier? file site.start site.stop Name.anonymous then
      addSqlHoverInfo identifier comparison
  for occurrence in site.occurrences do
    if let some bindings := foundColumns? occurrence then
      let name := (occurrence.name.map (Name.mkSimple ∘ toString)).getD Name.anonymous
      if let some identifier := source.identifier? file site.start site.stop name then
        addSqlColumnInfo identifier (columnDescription catalog bindings)
  if let some (name, use, candidates) := unknownName? site then
    emitUnknownName source file bytes site name use candidates

end Belay.Sqlite
