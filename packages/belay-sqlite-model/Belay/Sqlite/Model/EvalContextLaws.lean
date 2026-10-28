import Belay.Sqlite.Model.ExprFault

set_option doc.verso true

/-! Context operations shared by expression and query proofs. -/

namespace Belay.Sqlite.Model.Resolved

/-- For the given context: the results of each subquery do not depend on the outer row. The
plain context of a clock value ({name}`EvalContext.plain`), in which key terms and filters are
evaluated, satisfies it. -/
def EvalContext.RowFree (context : EvalContext) : Prop :=
  ∀ index row other, context.subqueries index row = context.subqueries index other

/-- For every clock value, the plain context of the clock value satisfies
{name}`EvalContext.RowFree`: each subquery gives no rows for every outer row. Proof sketch: the
definition. -/
theorem EvalContext.plain_rowFree (clock : Int) : (EvalContext.plain clock).RowFree := fun _ _ _ => rfl

/-- The context with the given results for the subqueries, by index, for every outer row; the other
fields are those of the context. An index past the list gives no row and no fault. For example,
{lit}`context.withRuns [run]` serves subquery 0 with {lit}`run`. -/
def EvalContext.withRuns (context : EvalContext) (runs : List SubqueryRun) : EvalContext :=
  { context with subqueries := fun index _ => (runs[index]?).getD { rows := [], fault := .none } }

/-- For every context, list of results, index and outer row, subquery {lit}`index` of the context with the results is
the result at that index of the list, or no row and no fault past the list. Proof sketch: the definition
computes. -/
theorem EvalContext.withRuns_subqueries (context : EvalContext) (runs : List SubqueryRun) (index : Nat) (outer : List Value) :
    (context.withRuns runs).subqueries index outer = (runs[index]?).getD { rows := [], fault := .none } := rfl

/-- For every context and list of results, the values bound to the parameters of the context with the results are
those of the context. Proof sketch: the definition computes. -/
theorem EvalContext.withRuns_parameters (context : EvalContext) (runs : List SubqueryRun) :
    (context.withRuns runs).parameters = context.parameters := rfl

/-- The result of a subquery with its first row marked certain. A scalar subquery reads that mark; {lit}`EXISTS` and
{lit}`IN` do not. -/
def SubqueryRun.certainFirst (run : SubqueryRun) : SubqueryRun := { run with firstCertain := true }

/-- For every result, marking its first row certain keeps its rows. Proof sketch: the definition computes. -/
@[simp] theorem SubqueryRun.certainFirst_rows (run : SubqueryRun) : run.certainFirst.rows = run.rows := rfl

/-- For every result, marking its first row certain keeps its fault. Proof sketch: the definition computes. -/
@[simp] theorem SubqueryRun.certainFirst_fault (run : SubqueryRun) : run.certainFirst.fault = run.fault := rfl

/-- For every result, marking its first row certain keeps the certainty of its rows. Proof sketch: the definition
computes. -/
@[simp] theorem SubqueryRun.certainFirst_rowsCertain (run : SubqueryRun) : run.certainFirst.rowsCertain = run.rowsCertain := rfl

/-- For every result, marking its first row certain makes the first row certain. Proof sketch: the definition
computes. -/
@[simp] theorem SubqueryRun.certainFirst_firstCertain (run : SubqueryRun) : run.certainFirst.firstCertain = true := rfl

end Belay.Sqlite.Model.Resolved
