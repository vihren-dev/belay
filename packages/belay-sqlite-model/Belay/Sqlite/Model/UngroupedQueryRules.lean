import Belay.Sqlite.Model.PlainQueryRules
import Belay.Sqlite.Model.SelectSubqueryRules
import Belay.Sqlite.Model.SelectAggregateRules

set_option doc.verso true

/-! The rules of an aggregate query without {lit}`GROUP BY` (ADR 0027, D1): its one group is the
rows that {lit}`WHERE` keeps, so it has one result row, also when no row is kept, and it fails exactly
when an aggregate fails over the kept rows. {lit}`SELECT sum(c) FROM t WHERE p` is such a query. -/

namespace Belay.Sqlite.Model.Resolved

/-- Ungrouped overflow rule: for every context, rows and query with aggregates
({lit}`query.aggregate = true`), without {lit}`GROUP BY` and with a {lit}`LIMIT` other than 0, the
query fails ({name}`Query.fails`) exactly when an aggregate fails ({name}`Aggregate.fails`) over the rows
that {lit}`WHERE` keeps: a hidden aggregate of the query or an aggregate result column. For example, the
query {lit}`SELECT sum(c) FROM t` fails exactly when the sum of the column overflows. Proof sketch: the
one group is the kept rows ({name}`queryGroups_ungrouped`). -/
theorem Query.fails_ungrouped (context : EvalContext) {query : Query} (aggregate : query.aggregate = true)
    (ungrouped : query.groupBy = []) (limit : query.limit ≠ some 0) (rows : List (List Value)) :
    query.fails context rows =
      (query.aggregates.any (·.fails context (filtered context query rows)) || query.columns.any fun
        | .aggregate aggregate => aggregate.fails context (filtered context query rows)
        | .scalar _ => false) := by
  have someLimit : (query.limit != some 0) = true := by simpa using limit
  simp only [Query.fails, aggregate, someLimit, queryGroups_ungrouped context ungrouped, Bool.true_and,
    List.any_cons, List.any_nil, Bool.or_false]
  rfl

/-- Ungrouped result rule: for every context, rows and query with aggregates, that is no compound
and has no {lit}`DISTINCT`, {lit}`GROUP BY`, {lit}`HAVING`, {lit}`ORDER BY`, {lit}`OFFSET` or
{lit}`LIMIT`, the possible results are one result of one row: the row of the group of the rows that
{lit}`WHERE` keeps ({name}`Query.groupRecord`). This also holds when no row is kept: for example,
{lit}`SELECT count(*) FROM t WHERE false` has the one row {lit}`0`. Proof sketch: the result law of a
query without order or window ({name}`Query.possibleResults_unordered`) with the one record of the
ungrouped rule ({name}`records_ungrouped`); the normal form of one row is the row. -/
theorem Query.possibleResults_ungrouped (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (aggregate : query.aggregate = true) (ungrouped : query.groupBy = [])
    (noHaving : query.having = none) (unordered : query.orderBy = []) (noOffset : query.offset = 0)
    (noLimit : query.limit = none) (rows : List (List Value)) :
    query.possibleResults context rows = [[(query.groupRecord context (filtered context query rows)).1]] := by
  rw [Query.possibleResults_unordered context unordered noOffset noLimit,
    Query.results_unordered context single noDistinct unordered noOffset noLimit,
    records_ungrouped context aggregate ungrouped noHaving]
  simp [normalForm, stableSort, insertStable]

/-- Ungrouped membership rule: for every context, query with the premises of
{name}`Query.possibleResults_ungrouped`, rows and result that the model permits for the query over the
rows, the result is the one row of the group of the rows that {lit}`WHERE` keeps
({name}`Query.groupRecord`). Proof sketch: {name}`Query.possibleResults_ungrouped` has one element. -/
theorem Query.mem_possibleResults_ungrouped (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (aggregate : query.aggregate = true) (ungrouped : query.groupBy = [])
    (noHaving : query.having = none) (unordered : query.orderBy = []) (noOffset : query.offset = 0)
    (noLimit : query.limit = none) {rows result : List (List Value)} (member : result ∈ query.possibleResults context rows) :
    result = [(query.groupRecord context (filtered context query rows)).1] := by
  rw [Query.possibleResults_ungrouped context single noDistinct aggregate ungrouped noHaving unordered noOffset
    noLimit] at member
  simpa using member

end Belay.Sqlite.Model.Resolved
