import Belay.Sqlite.Model.Schema.Dispatch.QueryJoinLaws

set_option doc.verso true

/-! Join rules of a SELECT (ADR 0027, D1, phase {lit}`source`): the complete rows of each join
kind as a collection, with their order and multiplicity. An inner join gives, for each left row in
order, the left row followed by each matching candidate in candidate order; a left join puts one
row with NULL cells in place of a left row without a match; a right join adds each candidate that
no left row matches after NULL cells, which keep the enclosing query's cells; a full join does both.
The cardinality rule counts the matches of each left row. -/

namespace Belay.Sqlite.Model.Resolved

/-- Two-table source rule: for every context, query whose sources are the table at one position
as the first source and then a join of the table at another position, and database with both
tables, the source rows of the query are the rows of the join ({name}`joinRows`) of the scans of
the two tables ({name}`sourceRows`), with the sum of their widths and no fault. Proof sketch: the
fold joins the first table to the one row without cells, which keeps its rows, then the second. -/
theorem Query.source_two_tables (context : EvalContext) (query : Query) (database : Database)
    {firstPosition secondPosition : Nat} {join : QuerySource} {first second : Table}
    (sources : query.sources = [QuerySource.first firstPosition, join]) (isTable : join.source = .table secondPosition)
    (firstPresent : database.table firstPosition = some first) (secondPresent : database.table secondPosition = some second) :
    query.source context database = some
      { rows := joinRows context first.shape.columns.length (sourceRows first) join second.shape.columns.length
          (sourceRows second) [],
        width := first.shape.columns.length + second.shape.columns.length, fault := .none } := by
  simp [Query.source, sources, List.foldlM, QuerySource.join, QuerySource.first, QuerySource.joinTable, joinRows,
    joinRow, joinMatches, QuerySource.matches, bind, Option.bind, pure, firstPresent, secondPresent, isTable]

end Belay.Sqlite.Model.Resolved
