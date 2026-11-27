import Belay.Sqlite.Model.Queries.Evaluation.ExprAppendLaws
import Belay.Sqlite.Model.Queries.Evaluation.SelectCalmRule

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- The meaning of a resolved expression with its parameters bound. An expression that
reads no columns has one value and fault for the scan. Other expressions read a row. -/
inductive CompiledExpr where
  /-- The value and fault shared by all input rows. -/
  | constant (result : Value × Resolved.Fault)
  /-- A function of the current row, for example the SQL sum of two column values. -/
  | perRow (run : List Value → Value × Resolved.Fault)

/-- Compile an expression in the SELECT's bound context. For example, a bound parameter
is constant across rows but its value depends on this statement's argument list. -/
def CompiledExpr.compile (args : List Value) (e : Resolved.Expr) : CompiledExpr :=
  let evaluate := e.evaluate (.bound args)
  if e.readsBelow 0 then .constant (evaluate []) else .perRow evaluate

/-- Read the value and fault of a compiled expression on the supplied row. -/
def CompiledExpr.run : CompiledExpr → List Value → Value × Resolved.Fault
  | .constant result => fun _ => result
  | .perRow f => f

/-- For every expression, argument list and row, compilation preserves both the SQL value
and the fault. Proof sketch: a bound context has no row-dependent subqueries. With no
column references, appending the entire row to the empty row preserves evaluation. -/
theorem CompiledExpr.run_compile (args : List Value) (e : Resolved.Expr) (row : List Value) :
    (compile args e).run row = e.evaluate (.bound args) row := by
  unfold compile
  split
  · rename_i closed
    exact (Resolved.Expr.evaluate_append (.bound args) (fun _ _ _ => rfl) [] row
      (width := 0) (by decide) e (by simpa [Resolved.Expr.readsBelow] using closed)).1.symm
  · rfl

end Belay.Sqlite
