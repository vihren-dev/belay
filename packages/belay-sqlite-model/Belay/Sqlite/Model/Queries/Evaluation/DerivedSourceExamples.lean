import Belay.Sqlite.Model.Shared.Execution.Execution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.DerivedSourceExamples

/-- A query of the supplied columns with no source and no window. -/
def select (columns : List Output) : Query :=
  { sources := [], filter := none, aggregate := false, groupBy := [], columns,
    names := columns.map fun _ => "value", orderBy := [], offset := 0, limit := none }

/-- A fixed source of two integer columns, with equal first values and different second values. -/
def pairs : QuerySource :=
  { kind := .inner, source := .pragma (.fixed 2 [[.integer 1, .integer 2], [.integer 1, .integer 3]]),
    condition := none }

/-- Select both columns of the fixed source, with the optional limit. -/
def pairQuery (limit : Option Nat := none) : Query :=
  { select [.scalar (.column 0), .scalar (.column 1)] with sources := [pairs], limit }

/-- A query that reads the complete two-column result of indexed subquery 0. -/
def fromPairs : Query :=
  { pairQuery with sources := [{ kind := .inner, source := .subquery 0 2, condition := none }] }

/-- Join one fixed value to a one-column indexed source under the supplied join kind. -/
def joined (kind : JoinKind) : Query :=
  { select [.scalar (.column 0), .scalar (.column 1)] with
    sources := [{ kind := .inner, source := .pragma (.fixed 1 [[.integer 9]]), condition := none },
      { kind, source := .subquery 0 1, condition := some (.literal (.integer 0)) }] }

/-- A constant result for the joined source. -/
def constant : Query := select [.scalar (.literal (.integer 4))]

/-- The enclosing row survives an empty left source before a correlated right join. -/
def correlated : Query :=
  { select [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2)] with
    outer := 1,
    sources := [{ kind := .inner, source := .pragma (.fixed 1 []), condition := none },
      { kind := .right, source := .subquery 0 1, condition := none }] }

end Belay.Sqlite.Model.Resolved.DerivedSourceExamples
