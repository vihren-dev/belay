import Belay.Sqlite.Model.Queries.Select.ResolveReadsBelow
import Belay.Sqlite.Model.Queries.Select.TableChecks

set_option doc.verso true

namespace Belay.Sqlite.Model

open Resolved

open Resolved

/-- For every scope that ends below a width, double-quote setting, condition, label, source text and
check: if the CHECK constraint resolves to the check ({name}`resolveCheck`), its condition reads below
the width. A refused constraint requires nothing. Proof sketch: the condition is the resolved operand
({name}`resolveOperand_below`). -/
theorem resolveCheck_below {width : Nat} {scope : Scope} (bounded : scope.Bounded width) {dqs : Bool}
    {condition : Syntax.Expr} {label : String} {text : Syntax.SourceText} {check : CheckConstraint}
    (ok : resolveCheck dqs scope condition label text = .ok check) :
    check.condition.any (Expr.isColumnFrom width) = false := by
  simp only [resolveCheck, exceptBind_eq_ok, condition_eq_ok] at ok
  obtain ⟨_, _, resolved, ⟨operand, ho, rfl⟩, ok⟩ := ok
  have := resolveOperand_below bounded dqs {} true condition operand ho
  split at ok
  · cases ok
  · cases ok; exact this

end Belay.Sqlite.Model
