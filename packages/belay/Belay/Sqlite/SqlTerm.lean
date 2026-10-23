import Lean.Elab.Term
import Belay.Sqlite.Model.Codec.Resolution
import Belay.Sqlite.Translation
import Belay.Sqlite.Script
import Belay.Sqlite.SqlLiteral

set_option doc.verso true

/-! {lit}`sql r"..."` (ADR 0017, D3 and D4): a {lit}`Script` of the statements of the SQL text,
which the translation reads while the file elaborates. SQL that SQLite's grammar rejects, and a
form that the translation refuses, is an elaboration error at its position in the text. The
term does not resolve the statements; each one resolves when it runs. -/

namespace Belay.Sqlite

open Lean Elab Term

/-- {lit}`sql "SQL"`: the script of the statements of the SQL text. For example,
{lit}`sql r"BEGIN; COMMIT"` is a script of two statements. A file that imports the surface reads
{lit}`sql` as this keyword, so a name {lit}`sql` there is written {lit}`«sql»`. -/
syntax (name := sqlTerm) "sql " str : term

/-- The statements of the SQL text with their ranges, translated with the grammar of the
default release, or the refusal. -/
def translateText (text : String) :
    IO (Except Translation.Refusal (Array (Translation.Located Belay.Sqlite.Model.Syntax.Statement))) := do
  let grammar ← IO.ofExcept ((selectGrammar (← loadedMetadata) Release.default).mapError IO.userError)
  Translation.translate grammar text.toUTF8

/-- The statements of the literal's SQL text, or an error at the position where SQLite's grammar
rejects the text or the translation refuses a form. -/
def literalStatements (literal : Syntax) : TermElabM (Array (Translation.Located Belay.Sqlite.Model.Syntax.Statement)) := do
  let some text := literal.isStrLit? | throwUnsupportedSyntax
  match ← (translateText text : IO _) with
  | .ok items => return items
  | .error refusal =>
    throwErrorAt (textRange literal text refusal.start (max refusal.stop (refusal.start + 1))) refusal.message

/-- The term of the script of the statements, each with no values, which {lit}`sql` gives and
{lit}`sql!` gives too, so that the two terms are equal by {lit}`rfl`. -/
def scriptExpr (items : Array (Translation.Located Belay.Sqlite.Model.Syntax.Statement)) : Expr :=
  mkApp (mkConst ``Script.mk) (toExpr (items.toList.map fun item => (item.value, ([] : List Belay.Sqlite.Model.Value))))

/-- Elaborate {lit}`sql "SQL"` to the script of its statements. -/
@[term_elab sqlTerm]
def elabSql : TermElab := fun term _ => do
  return scriptExpr (← literalStatements term[1])

end Belay.Sqlite
