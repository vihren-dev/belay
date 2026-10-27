import Belay.Sqlite.Model.Resolution.SyntaxReindex

set_option doc.verso true

/-! The identity re-indexing of written syntax (ADR 0017, S6). Resolving a write copies its expressions
with {lit}`Syntax.Expr.reindex` and the identity function, so a law about a written expression can
state its premises about the expression itself. -/

namespace Belay.Sqlite.Model.Syntax

mutual
/-- For every expression, changing every query index with the identity function keeps the expression.
Proof sketch: induction over the mutual expression and list types; each constructor rebuilds its
parts from themselves, and the index functions give the same indexes. -/
theorem Expr.reindex_id_aux : ∀ expression : Expr, Id.run (expression.reindexM (pure : Nat → Id Nat)) = expression
  | .negate operand => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .positive operand => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .compare operator left right => by simp [Expr.reindexM, Expr.reindex_id_aux left, Expr.reindex_id_aux right]
  | .and left right => by simp [Expr.reindexM, Expr.reindex_id_aux left, Expr.reindex_id_aux right]
  | .or left right => by simp [Expr.reindexM, Expr.reindex_id_aux left, Expr.reindex_id_aux right]
  | .not operand => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .isNull operand negated => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .call name arguments => by simp [Expr.reindexM, Expr.reindexList_id_aux arguments]
  | .arithmetic operator left right => by simp [Expr.reindexM, Expr.reindex_id_aux left, Expr.reindex_id_aux right]
  | .cast operand typeName => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .collate operand name => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .exists child => by simp [Expr.reindexM]
  | .inQuery operand child negated => by simp [Expr.reindexM, Expr.reindex_id_aux operand]
  | .subquery child => by simp [Expr.reindexM]
  | .inList operand values negated => by
    simp [Expr.reindexM, Expr.reindex_id_aux operand, Expr.reindexList_id_aux values]
  | .between operand low high negated => by
    simp [Expr.reindexM, Expr.reindex_id_aux operand, Expr.reindex_id_aux low, Expr.reindex_id_aux high]
  | .caseOf operands hasBase => by simp [Expr.reindexM, Expr.reindexList_id_aux operands]
  | .concatenate left right => by simp [Expr.reindexM, Expr.reindex_id_aux left, Expr.reindex_id_aux right]
  | .raise kind (some message) => by simp [Expr.reindexM, Expr.reindex_id_aux message]
  | .null => rfl
  | .numeric text => rfl
  | .string bytes => rfl
  | .blob bytes => rfl
  | .parameter number => rfl
  | .currentTime keyword => rfl
  | .identifier name quote => rfl
  | .qualified source column schema => rfl
  | .callStar name => rfl
  | .raise kind none => rfl

/-- For every list of expressions, changing every query index with the identity function keeps the list.
Proof sketch: induction on the list with {name}`Expr.reindex_id_aux`. -/
theorem Expr.reindexList_id_aux : ∀ expressions : List Expr,
    Id.run (Expr.reindexListM (pure : Nat → Id Nat) expressions) = expressions
  | [] => rfl
  | first :: rest => by simp [Expr.reindexListM, Expr.reindex_id_aux first, Expr.reindexList_id_aux rest]
end

/-- For every written expression, {name}`Expr.reindex` with the identity function is the expression.
In plain words, copying syntax without changing the query indexes changes nothing. Proof sketch:
{name}`Expr.reindex_id_aux`. -/
theorem Expr.reindex_id (expression : Expr) : expression.reindex id = expression :=
  by simpa [Expr.reindex, Function.comp_def] using Expr.reindex_id_aux expression

end Belay.Sqlite.Model.Syntax
