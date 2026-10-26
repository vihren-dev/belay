import Belay.Sqlite.SqlEditorSource
import Belay.Sqlite.SqlParameters
import Lean.Elab.Term

set_option doc.verso true

/-! Emit SQL parameter hovers and native semantic tokens from the existing {name (full := Belay.Sqlite.ParameterPlan)}`ParameterPlan`.
Keep captured Lean expressions before coercion so users can inspect their original types. -/

namespace Belay.Sqlite
open Lean Elab Term

/-- Attach the original Lean expression and a SQL description to one mapped occurrence.
Ordinary term information supplies native variable coloring. Its nested description supplies
the hover text while retaining the same expression and local context. -/
def addSqlParameterInfo (stx : Syntax) (expression : Expr) (description : String) : TermElabM Unit := do
  let term : TermInfo :=
    { stx := stx, expr := expression, lctx := ← getLCtx, elaborator := .anonymous, expectedType? := none }
  let value ← Meta.ppExpr expression
  let type ← Meta.ppExpr (← Meta.inferType expression)
  let hover := s!"```lean\n{value} : {type}\n```\n\n{description}"
  let detail : DelabTermInfo := { term with mkDocString? := some fun _ => pure hover }
  let children := ({} : PersistentArray InfoTree).push (.node (.ofDelabTermInfo detail) {})
  pushInfoTree (.node (.ofTermInfo term) children)

/-- Emit information for every parameter occurrence using its existing plan slot and SQLite
number. The supplied expressions are the actual captured Lean values before coercion or the
generated argument locals. For example, repeated {lit}`$name` occurrences retain the type
of the captured {lit}`name`; {lit}`?3` describes argument {lit}`p3` and SQLite number 3.
Missing expressions or inexact source mappings emit nothing and do not change the script. -/
def emitSqlParameterInfo (source : SqlEditorSource)
    (items : Array Translation.ParameterizedStatement) (plan : ParameterPlan)
    (expressions : List (ParameterSource × Expr)) : TermElabM Unit := do
  let file ← getFileMap
  for (item, slots) in items.toList.zip plan.slots do
    for parameter in item.parameters do
      let some (.source binding) := slots[parameter.number - 1]? | continue
      let some expression := expressions.lookup binding | continue
      let some stx := source.identifier? file parameter.start parameter.stop
        (Name.mkSimple binding.name) | continue
      let origin := match binding with
        | .variable name => s!"Captured Lean value `{name}`"
        | .argument name => s!"Generated argument `{name}`"
      addSqlParameterInfo stx expression
        s!"SQL parameter `{parameter.text}`. {origin}; SQLite parameter number {parameter.number}."

end Belay.Sqlite
