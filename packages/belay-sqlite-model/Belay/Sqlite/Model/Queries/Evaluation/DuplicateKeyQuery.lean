import Belay.Sqlite.Model.Queries.Evaluation.QueryEval

set_option doc.verso true

/-! The duplicate-key query of ADR 0017, S4 and S6: {lit}`SELECT c FROM t [WHERE w] GROUP BY k HAVING count(*) > 1`. It
keeps the rows of the table for which {lit}`w` is true, groups them by the key {lit}`k` under a collation and keeps
the groups of more than one row, so it has a row exactly when two such rows have a key that is equal under the
collation. NULL keys are equal here, unlike in a {lit}`UNIQUE` index. The phase rules of ADR 0027 give its results;
the fixture {lit}`tests/surface/SelectDuplicateKeySupport.lean` applies them. -/

namespace Belay.Sqlite.Model.Resolved

/-- The duplicate-key query of the given sources, optional {lit}`WHERE` condition, result column with its name, grouping
key and collation: an aggregate query with the one grouping term, the one result column, the one aggregate
{lit}`count(*)` and the condition {lit}`HAVING count(*) > 1`, and without ordering, window, {lit}`DISTINCT` or
compound, that reads no cell of an outer query. The result column is the literal one named {lit}`"1"` for the query
of S4, and a grouped expression such as the key for the query of the guide. -/
def Query.duplicateKeys (sources : List QuerySource) (filter : Option Expr) (column : Expr) (name : String) (key : Expr)
    (collation : Collation) : Query :=
  { sources, filter, aggregate := true, groupBy := [(key, collation)],
    columns := [.scalar column], names := [name], orderBy := [], offset := 0, limit := none,
    limitParameter := none, offsetParameter := none, outer := 0, aggregates := [.countRows],
    having := some (.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary), distinct := none }

/-- The rows that a {lit}`WHERE` condition keeps: those for which it is true, or all rows when there is no condition. -/
def keptRows (context : EvalContext) (filter : Option Expr) (rows : List (List Value)) : List (List Value) :=
  rows.filter fun row => filter.all fun condition => truthy (condition.eval context row)

/-- Without a {lit}`WHERE` condition, every row is kept. Proof sketch: the filter keeps a row when the condition is absent. -/
theorem keptRows_none (context : EvalContext) (rows : List (List Value)) : keptRows context none rows = rows :=
  List.filter_eq_self.2 (by simp)

end Belay.Sqlite.Model.Resolved
