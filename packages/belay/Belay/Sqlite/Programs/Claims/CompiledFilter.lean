import Belay.Sqlite.Programs.Claims.ExprOrder
import Belay.Sqlite.Programs.Claims.CompiledExpr

set_option doc.verso true

namespace Belay.Sqlite.CompiledScript
open Model Resolved

/-- A WHERE test keeps its sign and the bindings of its statement when scans compose. -/
structure FilterAtom where
  /-- Resolved test before SQL truth conversion. -/
  expression : Resolved.Expr
  /-- Complement row acceptance for a preceding DELETE. -/
  complemented : Bool
  /-- Parameters of the statement that supplied the test. -/
  args : List Value
  deriving DecidableEq

local instance : Ord Resolved.Expr := ⟨exprOrder⟩
local instance : Ord Value := instOrdValue
deriving instance Ord for FilterAtom

/-- Whether this signed test accepts the row. The complement applies after SQL truth conversion. -/
def FilterAtom.accepts (a : FilterAtom) (outer : List Value) (row : List Value) : Bool :=
  Resolved.truthy (a.expression.eval (.bound (a.args ++ outer)) row) != a.complemented

/-- No clauses accepts everything. The outer none rejects everything. -/
abbrev Filter := Option (List FilterAtom)

/-- Test all clauses of a compiled WHERE. -/
def Filter.accepts (f : Filter) (outer : List Value) (row : List Value) := f.any (·.all (·.accepts outer row))

/-- Scan only when the filter can accept a row. -/
def Filter.rows (f : Filter) (source : Unit → List (List Value)) : List (List Value) :=
  match f with
  | none => []
  | some [] => source ()
  | some atoms => (source ()).filter fun row => atoms.all (·.accepts [] row)

/-- Filtering by the canonical clauses gives precisely their accepted rows.
Proof sketch: split on the empty, rejecting and nonempty cases. -/
theorem Filter.rows_eq (f : Filter) (xs : List (List Value)) :
    f.rows (fun _ => xs) = xs.filter (f.accepts []) := by
  cases f with
  | none => simp [rows, accepts]
  | some atoms =>
    cases atoms with
    | nil => exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
    | cons _ _ => rfl

/-- Insert a clause in structural order, keeping one copy. Structural recursion keeps the
normalizer reducible in the kernel, including when a caller proves a plan equality by reflexivity. -/
private def insertAtom (a : FilterAtom) : List FilterAtom → List FilterAtom
  | [] => [a]
  | b :: bs =>
    if a = b then b :: bs
    else if (compare a b).isLE then a :: b :: bs else b :: insertAtom a bs

/-- Insertion adds one Boolean requirement. Proof sketch: duplicate requirements are
idempotent and the order of the remaining requirements does not affect conjunction. -/
private theorem all_insert (a : FilterAtom) (outer : List Value) (r : List Value) (xs : List FilterAtom) :
    (insertAtom a xs).all (·.accepts outer r) = (a.accepts outer r && xs.all (·.accepts outer r)) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    by_cases same : a = b
    · subst b
      simp [insertAtom]
    · simp [insertAtom, same]
      split <;> simp [ih, Bool.and_left_comm]

/-- Merge normalized clauses into a single ordered, duplicate-free conjunction. -/
def Filter.both (a b : Filter) : Filter := do
  let xs ← a
  let ys ← b
  return xs.foldr insertAtom ys

/-- Combining filters computes the conjunction of their acceptance tests.
Proof sketch: insert the clauses in turn and apply the insertion law. -/
theorem Filter.accepts_both (a b : Filter) (outer : List Value) (r : List Value) :
    (both a b).accepts outer r = (a.accepts outer r && b.accepts outer r) := by
  cases a with
  | none => rfl
  | some xs =>
    cases b with
    | none => simp [both, accepts]
    | some ys =>
      change (xs.foldr insertAtom ys).all _ = (xs.all _ && ys.all _)
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.foldr_cons, all_insert, ih, List.all_cons, Bool.and_assoc]

/-- Fold closed expressions with the model evaluator and retain row-dependent tests. -/
def Filter.atom (args : List Value) (e : Resolved.Expr) (neg : Bool) : Filter :=
  match CompiledExpr.compile args e with
  | .constant result => if Resolved.truthy result.1 != neg then some [] else none
  | .perRow _ => some [⟨e, neg, []⟩]

/-- For every binding, expression and row, a compiled atom accepts exactly when SQL
truth differs from the complement flag. Proof sketch: apply {name}`CompiledExpr.run_compile`. -/
theorem Filter.accepts_atom (args : List Value) (e : Resolved.Expr) (neg : Bool) (r : List Value) :
    (atom args e neg).accepts args r = (Resolved.truthy (e.eval (.bound args) r) != neg) := by
  have h := congrArg (fun result => Resolved.truthy result.1) (CompiledExpr.run_compile args e r)
  cases hp : CompiledExpr.compile args e with
  | constant v =>
    change Resolved.truthy ((CompiledExpr.compile args e).run r).1 = _ at h
    rw [hp] at h
    change Resolved.truthy v.1 = Resolved.truthy (e.eval (.bound args) r) at h
    simp [atom, hp, ← h, accepts]
    split <;> simp_all
  | perRow run => simp [atom, hp, accepts, FilterAtom.accepts]

/-- Lower AND to filter conjunction and IS NOT to the complement of IS. A negated
conjunction stays a single test because complementing all its clauses would change its meaning. -/
def Filter.expr (args : List Value) (neg : Bool) : Resolved.Expr → Filter
  | .and a b => if neg then atom args (.and a b) true else (expr args false a).both (expr args false b)
  | .compare .isNot aff a b coll => atom args (.compare .is aff a b coll) (!neg)
  | e => atom args e neg

/-- For every binding, row, flag and expression, {name}`Filter.expr` accepts the row
exactly when the bound expression is truthy and the flag is false, or the expression
fails the truth test and the flag is true. Proof sketch: apply the
SQL AND and IS NOT truth laws and expression correctness for the remaining atoms. -/
theorem Filter.accepts_expr (args : List Value) (r : List Value) (neg : Bool) (e : Resolved.Expr) :
    (expr args neg e).accepts args r = (Resolved.truthy (e.eval (.bound args) r) != neg) := by
  fun_induction expr args neg e <;> simp_all [accepts_atom, accepts_both, Resolved.Expr.eval_and,
    Resolved.truthy_and, Resolved.Expr.eval_compare, Resolved.truthy_isNot]
  all_goals cases neg <;> simp_all

/-- Attach this statement's bindings after duplicate clauses have been removed. This
lets equal parameter slots normalize even when the supplied values are variables. -/
private def bindFilter (args : List Value) (f : Filter) : Filter :=
  f.map (List.map fun a => { a with args := a.args ++ args })

/-- Binding a normalized filter preserves its row test. Proof sketch: move the
statement's arguments into each clause and evaluate it on the same row. -/
private theorem accepts_bind (args : List Value) (f : Filter) (r : List Value) :
    (bindFilter args f).accepts [] r = f.accepts args r := by
  cases f <;> simp [bindFilter, Filter.accepts, List.all_map, Function.comp_def, FilterAtom.accepts]

/-- An absent WHERE selects every row. Its complement selects none. -/
def Filter.whereClause (args : List Value) (neg : Bool) : Option Resolved.Expr → Filter
  | none => if neg then none else some []
  | some e => bindFilter args (expr args neg e)

/-- For every binding, flag, optional predicate and row, {name}`Filter.whereClause` with
empty outer bindings accepts the row exactly when {name}`Resolved.conditionKeeps` differs from the flag.
Proof sketch: handle the absent WHERE and use expression normalization for a supplied predicate. -/
theorem Filter.accepts_where (args : List Value) (neg : Bool) (p : Option Resolved.Expr) (row : List Value) :
    (whereClause args neg p).accepts [] row = (Resolved.conditionKeeps p (.bound args) row != neg) := by
  cases p with
  | none => cases neg <;> rfl
  | some e => exact (accepts_bind ..).trans (accepts_expr args row neg e)

end Belay.Sqlite.CompiledScript
