import Belay

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! Grouping terms that are expressions through SQL and actual execution: a term groups by its
value without affinity, under its collation; an integer names a result column and other
literals are constants; an alias inside a term and a subquery in a term are model
restrictions. The corpus compares the same queries with native SQLite. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

namespace ExpressionGroupingExamples

/-- Four storage classes of one number and a column under {lit}`NOCASE`. -/
def database : Database := db! r"
  CREATE TABLE g(a, c TEXT COLLATE NOCASE, n);
  INSERT INTO g VALUES(1, 'a', 1), (1.0, 'A', 3), ('1', 'b', 2), (x'31', 'B', 5);"

/-- The model restriction of the first statement of a script, or none when it resolves or
stops with a native error. -/
def restriction (script : Script) : Option RestrictionKind := do
  let (statement, _) ← script.statements.head?
  match resolveStatement runContext database.raw.connection.resolveState statement with
  | .error issue => some issue.kind
  | .ok _ => none

/-- {lit}`a+0` puts the four rows in one group, and {lit}`a` as written in three groups:
{lit}`1` and {lit}`1.0` are equal, the text and the blob are other values. -/
theorem storage_classes : (database.run (sql r"
    SELECT count(*) FROM g GROUP BY a+0; SELECT count(*) FROM g GROUP BY a ORDER BY 1;")).outputs =
    [.rows [[.integer 4]], .rows [[.integer 1], [.integer 1], [.integer 2]]] := by
  decide +kernel

/-- An expression over {lit}`c` keeps the column's {lit}`NOCASE` through unary plus, and
{lit}`c || ''` compares under {lit}`BINARY`. -/
theorem collation_of_a_term : (database.run (sql r"
    SELECT count(*) FROM g GROUP BY +c; SELECT count(*) FROM g GROUP BY c || '';")).outputs =
    [.rows [[.integer 2], [.integer 2]], .rows [[.integer 1], [.integer 1], [.integer 1], [.integer 1]]] := by
  decide +kernel

/-- {lit}`+1` names result column 1, and {lit}`1.0` is a constant: one group. -/
theorem numbers_of_a_term : (database.run (sql r"
    SELECT c, count(*) FROM g GROUP BY +1 ORDER BY 2; SELECT count(*) FROM g GROUP BY 1.0;")).outputs =
    [.rows [[.text "a".toUTF8.toList, .integer 2], [.text "b".toUTF8.toList, .integer 2]], .rows [[.integer 4]]] := by
  decide +kernel

/-- An alias inside a term and a subquery in a term are model restrictions. -/
theorem refused_terms :
    restriction (sql r"SELECT a AS k FROM g GROUP BY k+1") = some .aliasInExpression ∧
    restriction (sql r"SELECT count(*) FROM g GROUP BY (SELECT 1)") = some .groupByTerm := by
  decide +kernel

#print axioms storage_classes
#print axioms collation_of_a_term
#print axioms numbers_of_a_term
#print axioms refused_terms
