import Belay.Sqlite.Model.Schema.Dispatch.SelectStepKeeps
import Belay.Sqlite.Model.Queries.Preparation.TwoStateQuery
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateQuery

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every statement whose form {name}`Syntax.Statement.asQuery?` reads as a query, the
statement is a SELECT with some parts. Proof sketch: by the cases of the statement. -/
theorem Syntax.Statement.select_of_asQuery {statement : Syntax.Statement} (query : statement.asQuery?.isSome = true) :
    ∃ columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
      statement = .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound := by
  cases statement <;> simp_all [Syntax.Statement.asQuery?]

end Belay.Sqlite.Model
