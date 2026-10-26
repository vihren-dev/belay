import Belay.Sqlite.SqlEditorSource
import Belay.Sqlite.SqlParameterInfo
import Lean.Elab.Term

set_option doc.verso true

/-! Native editor information for a table name in SQL text: a hover with the catalog facts, a
go-to-definition target when the table has a known origin, and a semantic token. Lean offers
semantic coloring from term information only for local variables and for the field of a
projection, so a table name takes the field coloring ({lit}`property`) through the same syntax
node that Lean uses for a projection ({name}`Lean.Parser.Term.identProjKind`). -/

namespace Belay.Sqlite

open Lean Elab Term

/-- Attach a hover and an optional definition target to the identifier of a mapped table name.
The term information has the name as a string literal, so the server finds no Lean declaration to
jump to; only the origin {lit}`location?` is a target. The nested information supplies the hover
text, as for a parameter ({name}`addSqlParameterInfo`). -/
def addSqlTableInfo (identifier : Syntax) (name : String) (description : String)
    (location? : Option DeclarationLocation) : TermElabM Unit := do
  let stx := Syntax.node .none Parser.Term.identProjKind #[identifier]
  let term : TermInfo :=
    { stx, expr := mkStrLit name, lctx := ← getLCtx, elaborator := .anonymous, expectedType? := none }
  let detail : DelabTermInfo :=
    { term with mkDocString? := some fun _ => pure description, location?, explicit := false }
  let children := ({} : PersistentArray InfoTree).push (.node (.ofDelabTermInfo detail) {})
  pushInfoTree (.node (.ofTermInfo term) children)

end Belay.Sqlite
