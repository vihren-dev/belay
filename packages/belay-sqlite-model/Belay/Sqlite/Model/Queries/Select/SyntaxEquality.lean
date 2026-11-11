import Belay.Sqlite.Model.Shared.Syntax.SyntaxEquality

set_option doc.verso true

/-! Equality of expressions as written, by structural recursion, so that the kernel reduces it
in the proofs of conformance cases. The derived {lit}`BEq` of {lit}`Syntax.Expr`, a nested
inductive type, is not structural, and the kernel cannot reduce it. Resolution compares the
aggregate calls of a query with it (ADR 0018, D3). -/

namespace Belay.Sqlite.Model

/-- For every expression, it is the same as itself ({name}`Syntax.Expr.same`). Proof sketch:
induction over the expression and its lists; each constructor compares equal parts. -/
theorem Syntax.Expr.same_self (a : Syntax.Expr) : a.same a = true := by
  induction a using Syntax.Expr.rec (motive_2 := fun xs => Syntax.Expr.sameList xs xs = true)
    (motive_3 := fun x => x.all (fun e => e.same e) = true)
  all_goals first
    | simp_all [Syntax.Expr.same, Syntax.Expr.sameList]
    | (rename_i message _; cases message <;> simp_all [Syntax.Expr.same])

/-- The index of the first expression of the list that is the same as the given one
({name}`Syntax.Expr.same`), if any. -/
def Syntax.Expr.indexIn (expression : Syntax.Expr) (list : List Syntax.Expr) : Option Nat :=
  list.findIdx? (·.same expression)

/-- The expressions of the list without the later copies of an expression
({name}`Syntax.Expr.same`), in order. -/
def Syntax.Expr.distinctList (list : List Syntax.Expr) : List Syntax.Expr :=
  list.foldl (fun kept expression => if kept.any (·.same expression) then kept else kept ++ [expression]) []

end Belay.Sqlite.Model
