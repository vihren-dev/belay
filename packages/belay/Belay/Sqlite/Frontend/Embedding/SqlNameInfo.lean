import Belay.Sqlite.Frontend.Grammar.SqlNameCorrections
import Belay.Sqlite.Frontend.Embedding.SqlEditorSource
import Lean.Elab.Term
import Lean.Meta.Tactic.TryThis

set_option doc.verso true

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

end Belay.Sqlite
