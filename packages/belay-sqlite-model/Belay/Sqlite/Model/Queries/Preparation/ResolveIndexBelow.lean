import Belay.Sqlite.Model.Queries.Select.ResolveTermsBelow
import Belay.Sqlite.Model.Queries.Preparation.IndexTerms

set_option doc.verso true

namespace Belay.Sqlite.Model

open Resolved

/-- For every scope that ends below a width and filter: if the filter of an index resolves to an
expression ({name}`indexFilter`), the expression reads below the width. A filter that is missing
or refused requires nothing. -/
theorem indexFilter_below {width : Nat} {dqs : Bool} {scope : Scope} (bounded : scope.Bounded width)
    {filter : Option Syntax.Expr} {resolved : Resolved.Expr}
    (ok : indexFilter dqs scope filter = .ok (some resolved)) : resolved.any (Expr.isColumnFrom width) = false := by
  cases filter with
  | none => cases ok
  | some term =>
    simp only [indexFilter, exceptBind_eq_ok, condition_eq_ok] at ok
    obtain ⟨_, _, _, _, found, ⟨operand, ho, rfl⟩, ok⟩ := ok
    have := resolveOperand_below bounded dqs {} true term operand ho
    split at ok
    · cases ok
    · simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok; exact this

end Belay.Sqlite.Model
