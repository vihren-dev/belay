import Belay.Sqlite.Tooling.Counterexamples.SqlNameDescription
import Belay.Sqlite.Queries.Preparation.SqlNameInfo

set_option doc.verso true

/-! The native editor information of the names that the name trace decided (the editor task,
part 2b): a hover and a semantic token for a column, a hover for a comparison, and, for a name that
no scope has, a warning for the double-quote fallback and the code actions that correct the name.
Lean derives semantic tokens from term information only for a local variable, so a column is
the local {lit}`variable` of the row, with the hover text of the resolver. The correction uses the
native "try this" mechanism, whose code action replaces exactly the range of the identifier. -/

namespace Belay.Sqlite

open Lean Elab Term Meta Belay.Sqlite.Model

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
