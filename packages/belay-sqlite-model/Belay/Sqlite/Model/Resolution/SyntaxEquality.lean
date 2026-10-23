import Belay.Sqlite.Model.Resolution.SyntaxExpr

set_option doc.verso true

/-! Equality of expressions as written, by structural recursion, so that the kernel reduces it
in the proofs of conformance cases. The derived {lit}`BEq` of {lit}`Syntax.Expr`, a nested
inductive type, is not structural, and the kernel cannot reduce it. Resolution compares the
aggregate calls of a query with it (ADR 0018, D3). -/

namespace Belay.Sqlite.Model

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
  | .exists i, .exists j | .subquery i, .subquery j | .parameter i, .parameter j => i == j
  | .inQuery a i n, .inQuery b j m => i == j && n == m && a.same b
  | .inList a xs n, .inList b ys m => n == m && a.same b && Syntax.Expr.sameList xs ys
  | .between a l h n, .between b k g m => n == m && a.same b && l.same k && h.same g
  | .caseOf xs n, .caseOf ys m => n == m && Syntax.Expr.sameList xs ys
  | .raise k none, .raise l none => k == l
  | .raise k (some a), .raise l (some b) => k == l && a.same b
  | .raise _ none, .raise _ (some _) | .raise _ (some _), .raise _ none => false
  | .null, _ | .numeric _, _ | .string _, _ | .blob _, _ | .parameter _, _ | .currentTime _, _ | .identifier .., _ | .qualified .., _
  | .negate _, _ | .positive _, _ | .compare .., _ | .and .., _ | .or .., _ | .not _, _ | .isNull .., _
  | .callStar _, _ | .call .., _ | .arithmetic .., _ | .cast .., _ | .collate .., _ | .exists _, _
  | .inQuery .., _ | .subquery _, _ | .inList .., _ | .between .., _ | .caseOf .., _ | .concatenate .., _
  | .raise .., _ => false

/-- Whether two lists of expressions are the same, item by item ({name}`Syntax.Expr.same`). -/
def Syntax.Expr.sameList : List Syntax.Expr → List Syntax.Expr → Bool
  | [], [] => true
  | a :: xs, b :: ys => a.same b && Syntax.Expr.sameList xs ys
  | _, _ => false
end

/-- For every expression, it is the same as itself ({name}`Syntax.Expr.same`). Proof sketch:
induction over the expression and its lists; each constructor compares equal parts. -/
theorem Syntax.Expr.same_self (a : Syntax.Expr) : a.same a = true := by
  induction a using Syntax.Expr.rec (motive_2 := fun xs => Syntax.Expr.sameList xs xs = true)
    (motive_3 := fun x => x.all (fun e => e.same e) = true)
  all_goals first
    | simp_all [Syntax.Expr.same, Syntax.Expr.sameList]
    | (rename_i message _; cases message <;> simp_all [Syntax.Expr.same])

/-- For every two expressions, they are the same ({name}`Syntax.Expr.same`) exactly when they are
equal. Proof sketch: induction over the first expression, its lists and its optional parts;
each constructor of the second is the same exactly when its parts are equal, by the induction
hypotheses. -/
theorem Syntax.Expr.same_iff (a : Syntax.Expr) : ∀ b, a.same b = true ↔ a = b := by
  induction a using Syntax.Expr.rec
      (motive_2 := fun xs => ∀ ys, Syntax.Expr.sameList xs ys = true ↔ xs = ys)
      (motive_3 := fun x => ∀ e, x = some e → ∀ b, e.same b = true ↔ e = b)
  case raise kind message ih =>
    intro b
    cases b with
    | raise other otherMessage =>
      cases message <;> cases otherMessage <;> simp_all [Syntax.Expr.same]
    | _ => simp [Syntax.Expr.same]
  case none => rename_i _ h _; cases h
  case some => rename_i _ inner _ h b; cases h; exact inner b
  all_goals first
    | (intro b; cases b <;> simp_all [Syntax.Expr.same, and_assoc, and_comm, and_left_comm])
    | (rename_i ys; cases ys <;> simp_all [Syntax.Expr.sameList])

/-- Equality of expressions as written, decided by {name}`Syntax.Expr.same`, which the kernel
reduces in proofs (the type is nested, so no derived instance exists). -/
instance : DecidableEq Syntax.Expr := fun a b => decidable_of_iff _ (Syntax.Expr.same_iff a b)

/-- The index of the first expression of the list that is the same as the given one
({name}`Syntax.Expr.same`), if any. -/
def Syntax.Expr.indexIn (expression : Syntax.Expr) (list : List Syntax.Expr) : Option Nat :=
  list.findIdx? (·.same expression)

/-- The expressions of the list without the later copies of an expression
({name}`Syntax.Expr.same`), in order. -/
def Syntax.Expr.distinctList (list : List Syntax.Expr) : List Syntax.Expr :=
  list.foldl (fun kept expression => if kept.any (·.same expression) then kept else kept ++ [expression]) []

end Belay.Sqlite.Model
