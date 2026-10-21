import Belay.Sqlite.Resolution.SyntaxExpr

set_option doc.verso true

/-! Equality of expressions as written, by structural recursion, so that the kernel reduces it
in the proofs of conformance cases. The derived {lit}`BEq` of {lit}`Syntax.Expr`, a nested
inductive type, is not structural, and the kernel cannot reduce it. Resolution compares the
aggregate calls of a query with it (ADR 0018, D3). -/

namespace Belay.Sqlite

mutual
/-- Whether two expressions are the same as written: the same constructor with the same
parts. -/
def Syntax.Expr.same : Syntax.Expr → Syntax.Expr → Bool
  | .null, .null => true
  | .numeric a, .numeric b | .currentTime a, .currentTime b | .callStar a, .callStar b => a == b
  | .string a, .string b | .blob a, .blob b => a == b
  | .identifier a q, .identifier b r => a == b && q == r
  | .qualified s c, .qualified t d => s == t && c == d
  | .negate a, .negate b | .positive a, .positive b | .not a, .not b => a.same b
  | .compare o a b, .compare p c d => o == p && a.same c && b.same d
  | .arithmetic o a b, .arithmetic p c d => o == p && a.same c && b.same d
  | .and a b, .and c d | .or a b, .or c d | .concatenate a b, .concatenate c d => a.same c && b.same d
  | .isNull a n, .isNull b m => n == m && a.same b
  | .call n xs, .call m ys => n == m && Syntax.Expr.sameList xs ys
  | .cast a t, .cast b u => t == u && a.same b
  | .collate a n, .collate b m => n == m && a.same b
  | .exists i, .exists j | .subquery i, .subquery j => i == j
  | .inQuery a i n, .inQuery b j m => i == j && n == m && a.same b
  | .inList a xs n, .inList b ys m => n == m && a.same b && Syntax.Expr.sameList xs ys
  | .between a l h n, .between b k g m => n == m && a.same b && l.same k && h.same g
  | .caseOf xs n, .caseOf ys m => n == m && Syntax.Expr.sameList xs ys
  | _, _ => false

/-- Whether two lists of expressions are the same, item by item ({name}`Syntax.Expr.same`). -/
def Syntax.Expr.sameList : List Syntax.Expr → List Syntax.Expr → Bool
  | [], [] => true
  | a :: xs, b :: ys => a.same b && Syntax.Expr.sameList xs ys
  | _, _ => false
end

/-- The index of the first expression of the list that is the same as the given one
({name}`Syntax.Expr.same`), if any. -/
def Syntax.Expr.indexIn (expression : Syntax.Expr) (list : List Syntax.Expr) : Option Nat :=
  list.findIdx? (·.same expression)

/-- The expressions of the list without the later copies of an expression
({name}`Syntax.Expr.same`), in order. -/
def Syntax.Expr.distinctList (list : List Syntax.Expr) : List Syntax.Expr :=
  list.foldl (fun kept expression => if kept.any (·.same expression) then kept else kept ++ [expression]) []

end Belay.Sqlite
