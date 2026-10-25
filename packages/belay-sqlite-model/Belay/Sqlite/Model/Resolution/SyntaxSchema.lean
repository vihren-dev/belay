import Belay.Sqlite.Model.Resolution.Syntax

set_option doc.verso true

/-! Whether a query names a schema in one of its sources (ADR 0017, S6). Only a two-state query may
read {lit}`before.t`, so a stored view body and a trigger refuse it and a plain query ignores the
initial database. -/

namespace Belay.Sqlite.Model

/-- Whether a query has a source with a schema name, as {lit}`before.t` has: the first source or
a joined source. -/
def Syntax.Subquery.hasSchemaSource (query : Syntax.Subquery) : Bool :=
  query.source.any (·.schema.isSome) || query.joins.any (·.source.schema.isSome)

end Belay.Sqlite.Model
