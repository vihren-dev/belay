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

/-- The script without statements, the unit of {lit}`++`. -/
def empty : Script := ⟨[]⟩

/-- The statements of the first script, then the statements of the second. -/
instance : Append Script := ⟨fun first second => ⟨first.statements ++ second.statements⟩⟩

/-- For all scripts, the statements of {lit}`p ++ q` are those of {lit}`p`, then those of
{lit}`q`. Proof sketch: the definition of {lit}`++`. -/
@[simp] theorem statements_append (p q : Script) : (p ++ q).statements = p.statements ++ q.statements := rfl

/-- For every script, {lit}`Script.empty ++ p` is {lit}`p`. Proof sketch: the lists are equal. -/
@[simp] theorem empty_append (p : Script) : empty ++ p = p := rfl

/-- For every script, {lit}`p ++ Script.empty` is {lit}`p`. Proof sketch: the lists are equal
({lit}`List.append_nil`). -/
@[simp] theorem append_empty (p : Script) : p ++ empty = p := by
  cases p
  show Script.mk (_ ++ []) = _
  rw [List.append_nil]

/-- For all scripts, {lit}`(p ++ q) ++ r` is {lit}`p ++ (q ++ r)`, so a chain needs no
parentheses. Proof sketch: the lists are associative ({lit}`List.append_assoc`). -/
theorem append_assoc (p q r : Script) : p ++ q ++ r = p ++ (q ++ r) := by
  cases p; cases q; cases r
  show Script.mk (_ ++ _ ++ _) = Script.mk (_ ++ (_ ++ _))
  rw [List.append_assoc]

end Script

end Belay.Sqlite
