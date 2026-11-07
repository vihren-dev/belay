import Belay.Sqlite.Model.SimpleQueryLaws
import Belay.Sqlite.Model.SelectWindowRules

set_option doc.verso true

/-! The result rows of a simple query (ADR 0017, S4): a query without {lit}`ORDER BY` sorts nothing, so
its result rows are the output of the source rows that {lit}`WHERE` keeps, in the order of the source rows. The
subquery forms {lit}`x IN (SELECT c FROM t WHERE p)` and a scalar subquery read these rows. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every simple query, over any rows, the result rows are the output rows of the source rows that
{lit}`WHERE` keeps, in their order: a scalar column gives its value on the row, and an aggregate column gives the aggregate
over the list of that one source row (the simple query has no {lit}`GROUP BY`, but the formula does not exclude an
aggregate column). Proof sketch: a query without
{lit}`ORDER BY` has no sort term, so every two records are in order and the sort keeps their order
({name}`stableSort_of_total`); the window takes all records. -/
theorem Query.Simple.results_eq {query : Query} (simple : query.Simple) (context : EvalContext)
    (rows : List (List Value)) :
    query.results context rows = (filtered context query rows).map fun row => query.columns.map fun
      | .scalar expression => expression.eval context row
      | .aggregate aggregate => aggregate.eval context [row] := by
  unfold Query.results
  dsimp only
  rw [stableSort_of_total _ (by simp [simple.orderBy, compareSort])]
  simp [Query.uniqueRecords, simple.compound, simple.distinct, simple.limit, simple.offset, records, simple.aggregate,
    simple.orderBy, Function.comp_def]
  intro _ _ _ _
  rfl

end Belay.Sqlite.Model.Resolved
