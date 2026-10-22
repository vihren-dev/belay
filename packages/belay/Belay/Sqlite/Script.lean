import Belay.Sqlite.Model

set_option doc.verso true

/-! The surface's scripts (ADR 0017, D3): a fixed list of statements, as in a {lit}`.sql` file.
Scripts form a monoid under {lit}`++`, with {lit}`Script.empty` as its unit. The term
{lit}`sql r"..."` of {lit}`Belay/Sqlite/SqlTerm.lean` gives a script. -/

namespace Belay.Sqlite

/-- SQL text as data: its statements in order, as the translation gives them. For example,
{lit}`sql r"COMMIT"` is the script of one statement, {name}`Belay.Sqlite.Model.Syntax.Statement.commit`. -/
structure Script where
  /-- The statements, in the order of the text. -/
  statements : List Belay.Sqlite.Model.Syntax.Statement

namespace Script

/-- The script without statements, the unit of {lit}`++`. For example,
{assert}`Script.empty.statements = []`. -/
def empty : Script := ⟨[]⟩

/-- The statements of the first script, then the statements of the second. -/
instance : Append Script := ⟨fun first second => ⟨first.statements ++ second.statements⟩⟩

/-- For all scripts {lit}`p` and {lit}`q`, the statements ({name}`Script.statements`) of
{lit}`p ++ q` are those of {lit}`p`, then those of {lit}`q`. For example,
{lean}`(Script.empty ++ Script.empty).statements = Script.empty.statements ++ Script.empty.statements`.
Proof sketch: the definition of {lit}`++`. -/
@[simp] theorem statements_append (p q : Script) : (p ++ q).statements = p.statements ++ q.statements := rfl

/-- For every script {lit}`p`, {name}`Script.empty` before {lit}`p` gives {lit}`p`. Proof sketch:
the lists are equal by definition. -/
@[simp] theorem empty_append (p : Script) : empty ++ p = p := rfl

/-- For every script {lit}`p`, {name}`Script.empty` after {lit}`p` gives {lit}`p`. Proof sketch:
the lists are equal ({name}`List.append_nil`). -/
@[simp] theorem append_empty (p : Script) : p ++ empty = p := by
  cases p
  show Script.mk (_ ++ []) = _
  rw [List.append_nil]

/-- For all scripts {lit}`p`, {lit}`q` and {lit}`r`, {lit}`(p ++ q) ++ r` is {lit}`p ++ (q ++ r)`,
so a chain needs no parentheses. Proof sketch: list append is associative
({name}`List.append_assoc`). -/
theorem append_assoc (p q r : Script) : p ++ q ++ r = p ++ (q ++ r) := by
  cases p; cases q; cases r
  show Script.mk (_ ++ _ ++ _) = Script.mk (_ ++ (_ ++ _))
  rw [List.append_assoc]

end Script

end Belay.Sqlite
