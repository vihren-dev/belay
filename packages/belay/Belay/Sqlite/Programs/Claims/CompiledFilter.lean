import Belay.Sqlite.Programs.Claims.ExprOrder
import Belay.Sqlite.Programs.Claims.CompiledExpr
import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun

set_option doc.verso true

namespace Belay.Sqlite.CompiledScript
open Model Resolved

/-- Test a clause with the bindings of this SELECT. -/
private def keeps (args : List Value) (row : List Value) (e : Resolved.Expr) : Bool :=
  Resolved.truthy (e.eval (.bound args) row)

/-- No clauses accepts everything. The outer none rejects everything. -/
abbrev Filter := Option (List Resolved.Expr)

/-- Test all clauses of a compiled WHERE. -/
def Filter.accepts (f : Filter) (args : List Value) (row : List Value) := f.any (·.all (keeps args row))

/-- Scan only when the filter can accept a row. -/
def Filter.rows (f : Filter) (args : List Value) (source : Unit → List (List Value)) : List (List Value) :=
  match f with
  | none => []
  | some [] => source ()
  | some atoms => (source ()).filter fun row => atoms.all (keeps args row)

/-- Filtering by the canonical clauses gives precisely their accepted rows.
Proof sketch: split on the empty, rejecting and nonempty cases. -/
theorem Filter.rows_eq (f : Filter) (args : List Value) (xs : List (List Value)) :
    f.rows args (fun _ => xs) = xs.filter (f.accepts args) := by
  cases f with
  | none => simp [rows, accepts]
  | some atoms =>
    cases atoms with
    | nil => exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
    | cons _ _ => rfl

/-- Insert a clause in structural order, keeping one copy. Structural recursion keeps the
normalizer reducible in the kernel, including when a caller proves a plan equality by reflexivity. -/
private def insertAtom (a : Resolved.Expr) : List Resolved.Expr → List Resolved.Expr
  | [] => [a]
  | b :: bs =>
    if a = b then b :: bs
    else if (exprOrder a b).isLE then a :: b :: bs else b :: insertAtom a bs

/-- Insertion adds one Boolean requirement. Proof sketch: duplicate requirements are
idempotent and the order of the remaining requirements does not affect conjunction. -/
private theorem all_insert (a : Resolved.Expr) (args : List Value) (r : List Value) (xs : List Resolved.Expr) :
    (insertAtom a xs).all (keeps args r) = (keeps args r a && xs.all (keeps args r)) := by
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
theorem Filter.accepts_both (a b : Filter) (args : List Value) (r : List Value) :
    (both a b).accepts args r = (a.accepts args r && b.accepts args r) := by
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
def Filter.atom (args : List Value) (e : Resolved.Expr) : Filter :=
  match CompiledExpr.compile args e with
  | .constant result => if Resolved.truthy result.1 then some [] else none
  | .perRow _ => some [e]

/-- For every binding, expression and row, the filter from {name}`Filter.atom` accepts the row
exactly when the bound expression is truthy. Proof sketch: apply {name}`CompiledExpr.run_compile`. -/
theorem Filter.accepts_atom (args : List Value) (e : Resolved.Expr) (r : List Value) :
    (atom args e).accepts args r = Resolved.truthy (e.eval (.bound args) r) := by
  have h := congrArg (fun result => Resolved.truthy result.1) (CompiledExpr.run_compile args e r)
  cases hp : CompiledExpr.compile args e with
  | constant v =>
    change Resolved.truthy ((CompiledExpr.compile args e).run r).1 = _ at h
    rw [hp] at h
    change Resolved.truthy v.1 = Resolved.truthy (e.eval (.bound args) r) at h
    simp [atom, hp, ← h, accepts]
    split <;> simp_all
  | perRow run => simp [atom, hp, accepts, keeps]

/-- Flatten conjunctions, fold constant clauses, and keep one copy of each remaining test. -/
def Filter.expr (args : List Value) : Resolved.Expr → Filter
  | .and a b => (expr args a).both (expr args b)
  | e => atom args e

/-- For every row and binding, the compiled clauses accept the row exactly when the SQL
expression passes WHERE. Proof sketch: SQL truth distributes over AND after conversion
to a row acceptance test. Apply this law at each conjunction. -/
theorem Filter.accepts_expr (args : List Value) (e : Resolved.Expr) (row : List Value) :
    (expr args e).accepts args row = Resolved.truthy (e.eval (.bound args) row) := by
  fun_induction expr args e <;> simp_all [accepts_atom, accepts_both, Resolved.Expr.eval_and,
    Resolved.truthy_and]

end Belay.Sqlite.CompiledScript
