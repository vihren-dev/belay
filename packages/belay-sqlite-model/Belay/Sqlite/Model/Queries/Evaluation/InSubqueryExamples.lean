import Belay.Sqlite.Model.Queries.Evaluation.QueryExamples
import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.InSubqueryExamples

/-- The table with one column {lit}`name` and the given cells as rows, with rowids 1, 2, and so on. -/
def oneColumn (cells : List Value) : Table where
  shape := { columns := [{ name := (name! "x"), declaredType := none }] }
  rows := (cells.zipIdx 1).map fun (cell, rowid) => ⟨rowid, [cell]⟩

/-- The database with the outer table {lit}`t` at position 0 and the table {lit}`u` of the subquery at position 1. -/
def database (outerCells subqueryCells : List Value) : Database :=
  .ofTables [((name! "t"), oneColumn outerCells), ((name! "u"), oneColumn subqueryCells)]

/-- {lit}`SELECT k FROM t WHERE x NOT IN (SELECT c FROM u)`, with the collation of the {lit}`IN` test. The outer
query has one column, so the subquery sees one outer cell. -/
def keysNotIn (collation : Collation) : Query × List Query :=
  ({ sources := [.first 0], filter := some (.inQuery (.column 0) 0 (some .numeric) collation true),
     aggregate := false, groupBy := [], columns := [.scalar (.column 0)], names := ["k"], orderBy := [], offset := 0,
     limit := none }, [Query.oneTable 1 1 none [.column 1] ["c"]])

/-- {lit}`SELECT k FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.c = k)`, with the collation of the comparison. -/
def keysNotExists (collation : Collation) : Query × List Query :=
  ({ (keysNotIn .binary).1 with filter := some (.not (.exists 0)) },
   [Query.oneTable 1 1 (some (.compare .eq (some .numeric) (.column 1) (.column 0) collation)) [.literal (.integer 1)]
      ["1"]])

/-- {lit}`SELECT k FROM t WHERE x IN (SELECT c FROM u)`. -/
def keysIn : Query × List Query :=
  ({ (keysNotIn .binary).1 with filter := some (.inQuery (.column 0) 0 (some .numeric) .binary false) },
   (keysNotIn .binary).2)

/-- {lit}`SELECT k FROM t WHERE EXISTS (SELECT 1 FROM u WHERE u.c = k)`. -/
def keysExists : Query × List Query :=
  ({ (keysNotIn .binary).1 with filter := some (.exists 0) }, (keysNotExists .binary).2)

end Belay.Sqlite.Model.Resolved.InSubqueryExamples
