import Belay.Sqlite.Model.Resolution.QueryExprs
import Belay.Sqlite.Model.Queries.Preparation.ResolveAll

set_option doc.verso true

/-! Resolution of the {lit}`RETURNING` columns of an INSERT or UPDATE (ADR 0012,
slice 3a). SQLite resolves them as the result columns of a {lit}`SELECT` over the
written table, after the values and the filter: {lit}`*` is every column under its
defined name, an expression is evaluated over the written row and named by its
alias, the defined name of a bare column, or its source text. An aggregate is
SQLite's {lit}`misuse of aggregate function`. -/

namespace Belay.Sqlite.Model

/-- The field of {lit}`Syntax.Statement.delete` that holds its {lit}`RETURNING` columns. -/
def deleteReturningField : Nat := 2

end Belay.Sqlite.Model
