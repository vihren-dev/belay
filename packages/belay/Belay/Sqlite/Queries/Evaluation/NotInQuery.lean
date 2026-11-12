import Belay.Sqlite.Model

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Whether a statement is a {lit}`SELECT`, whatever its parts: it is {lit}`.select` of some result columns, source,
joins, filter, grouping, ordering, limit, offset, subqueries, having clause, distinct flag and compound part. Plain
words: the statement is a query statement of the select kind, and nothing else is said about it. -/
def IsSelectStatement (statement : Syntax.Statement) : Prop :=
  ∃ columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
    statement = .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound

end Belay.Sqlite
