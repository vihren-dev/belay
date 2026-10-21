import Belay.Sqlite.Model.Resolution.UsingExamples

set_option doc.verso true

/-! Examples of {lit}`RIGHT` and {lit}`FULL` joins (ADR 0012, amendment 3; slice 4c),
checked by {lit}`#guard`: the resolved kinds and the rows of the joins. -/

namespace Belay.Sqlite.Model.Resolution.RightJoinExamples
open Belay.Sqlite.Model Syntax Resolution.Examples Resolution.JoinExamples Resolution.UsingExamples

/-- A table of two rows, with {lit}`a` 1 and 3. -/
def rightTwo : Table :=
  { shape := { columns := [{ name := (name! "a"), declaredType := some "INTEGER" }] },
    rows := [{ rowid := 1, values := [.integer 1] }, { rowid := 2, values := [.integer 3] }] }

/-- A table without rows. -/
def empty : Table := { shape := { columns := [{ name := (name! "a"), declaredType := some "INTEGER" }] }, rows := [] }

/-- A join of the kind to table 1 with the condition. -/
def join (kind : Resolved.JoinKind) (condition : Option Resolved.Expr := equal) : Resolved.QuerySource :=
  { kind, source := .table 1, condition }

/-- The rows of a join of {name}`JoinExamples.left` (one column) and the table. -/
def rowsWith (kind : Resolved.JoinKind) (table : Table) (condition : Option Resolved.Expr := equal) :
    List (List Value) :=
  Resolved.joinRows (.plain 0) 1 (Resolved.sourceRows JoinExamples.left) (join kind condition) table.shape.columns.length
    (Resolved.sourceRows table)

-- The operators resolve to their kinds.
#guard (queryOver [.star] (table (name! "t")) [joined ["RIGHT"] (table (name! "u")) (some onA)]).map (fun query => (query.sources.drop 1).map (·.kind)) ==
  some [.right]
#guard (queryOver [.star] (table (name! "t")) [joined ["full", "Outer"] (table (name! "u")) (some onA)]).map (fun query => (query.sources.drop 1).map (·.kind)) ==
  some [.full]
-- A right join adds each unmatched right row padded on the left; a full join adds both sides.
#guard rowsWith .right rightTwo == [[.integer 1, .integer 1], [.null, .integer 3]]
#guard rowsWith .full rightTwo == [[.integer 1, .integer 1], [.integer 2, .null], [.null, .integer 3]]
-- An ON condition false for every row, and empty inputs.
#guard rowsWith .right rightTwo (some (.literal (.integer 0))) == [[.null, .integer 1], [.null, .integer 3]]
#guard rowsWith .full empty == [[.integer 1, .null], [.integer 2, .null]]
#guard rowsWith .right empty == []
#guard Resolved.joinRows (.plain 0) 1 [] (join .full) 1 (Resolved.sourceRows rightTwo) == [[.null, .integer 1], [.null, .integer 3]]

/-- A right join to table 2 on the second and third cells of the joined row. -/
def rightOnSecond : Resolved.QuerySource := { kind := .right, source := .table 2, condition := some (.compare .eq none (.column 1) (.column 2)) }

/-- A query of every cell of {name}`JoinExamples.left` full joined with table 1. -/
def fullQuery : Resolved.Query :=
  { sources := [.first 0, join .full], filter := none, aggregate := false, groupBy := [], columns := [],
    names := [], orderBy := [], offset := 0, limit := none }

-- After an inner join, a right join pads every column of the left input.
#guard Resolved.joinRows (.plain 0) 2 (rowsWith .inner rightTwo) rightOnSecond 1 (Resolved.sourceRows rightTwo) ==
  [[.integer 1, .integer 1, .integer 1], [.null, .null, .integer 3]]
-- The source of a query folds the joins with the width of the tables so far.
#guard (fullQuery.source (.plain 0) (.ofTables [((name! "l"), JoinExamples.left), ((name! "r"), rightTwo)])).map (·.rows) ==
  some [[.integer 1, .integer 1], [.integer 2, .null], [.null, .integer 3]]

end Belay.Sqlite.Model.Resolution.RightJoinExamples
