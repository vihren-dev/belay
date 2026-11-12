import Belay.Sqlite.Model.Schema.Writes.ScriptRunExamples
import Belay.Sqlite.Model.Queries.Preparation.InsertSelectExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- {lit}`CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER)` followed by an index on {lit}`x`: a source table
that SQLite may read by its scan or by the index. -/
def indexedSource : List Syntax.Statement :=
  [.createTable (name! "s") [{ name := name! "id", declaredType := some "INTEGER", constraints := [.primaryKey false] },
      column (name! "x") (some "INTEGER")] [],
    .createIndex (name! "sx") false (name! "s") [key (name! "x")] none]

/-- {lit}`CREATE TABLE s(x INTEGER)`: a source table without an index. -/
def plainSource : List Syntax.Statement := [.createTable (name! "s") [column (name! "x") (some "INTEGER")] []]

/-- {lit}`CREATE TABLE t(id INTEGER PRIMARY KEY, name INTEGER)`: the target at position 1 when the source
has one statement, and at position 1 also after {lit}`indexedSource`, which has one table. -/
def createTarget : Syntax.Statement :=
  .createTable (name! "t")
    [{ name := name! "id", declaredType := some "INTEGER", constraints := [.primaryKey false] },
      column (name! "name") (some "INTEGER")] []

/-- {lit}`INSERT INTO s(x) VALUES (?1)`; the value comes from the values of the statement. -/
def insertParameter : Syntax.Statement := .insert (name! "s") (some [name! "x"]) [[.parameter 1]] []

/-- {lit}`INSERT INTO t(name) SELECT x FROM s`, with the optional {lit}`WHERE` condition. -/
def copySource (filter : Option Expr := none) : Syntax.Statement :=
  .insertSelect (name! "t") (some [name! "name"])
    { columns := [.expression (.identifier (name! "x") .none) none "x"], source := some { table := name! "s", alias := none },
      joins := [], filter, groupBy := [], orderBy := [], limit := none, offset := none } []

/-- {lit}`x > 0`. -/
def positive : Expr := .compare .gt (.identifier (name! "x") .none) (.numeric "0")

/-- {lit}`INSERT INTO target SELECT abs(x) FROM source`. -/
def insertAbs (target source : String) : Syntax.Statement :=
  .insertSelect (Identifier.ofString target) none
    { columns := [.expression (.call "abs" [.identifier (name! "x") .none]) none "abs"],
      source := some { table := Identifier.ofString source, alias := none },
      joins := [], filter := none, groupBy := [], orderBy := [], limit := none, offset := none } []

/-- The values of the statements of a script that creates a source table, a target and inserts the
values 20 and 10 into the source: the statement at the index gets the item at the index. -/
def twoRows (setup : Nat) : List (List Value) := List.replicate setup [] ++ [[.integer 20], [.integer 10]]

/-- The script {lit}`indexedSource`, the target, two source rows and the copy of the rows with
{lit}`x > 0`, which SQLite answers by the index. -/
def indexedCopy : List Syntax.Statement :=
  indexedSource ++ [createTarget, insertParameter, insertParameter, copySource (some positive)]

/-- The same script for a source without an index. -/
def plainCopy : List Syntax.Statement :=
  plainSource ++ [createTarget, insertParameter, insertParameter, copySource (some positive)]

/-- The script of a source with the values 5 and the smallest integer, and an INSERT of their absolute
values into the target {lit}`t` or into the source itself, with a query of {lit}`last_insert_rowid()`. -/
def overflowScript (into : String) (target : List Syntax.Statement) : List Syntax.Statement :=
  plainSource ++ target ++ [insertParameter, insertParameter, insertAbs into "s", lastRowid]

/-- {lit}`CREATE TABLE t(id INTEGER PRIMARY KEY)`. -/
def createIdTarget : Syntax.Statement :=
  .createTable (name! "t") [{ name := name! "id", declaredType := some "INTEGER", constraints := [.primaryKey false] }] []

/-- The values of {lit}`overflowScript`: the two inserts into the source are after {lit}`setup` statements. -/
def overflowValues (setup : Nat) : List (List Value) :=
  List.replicate setup [] ++ [[.integer 5], [.integer (-9223372036854775808)]]

/-- {lit}`INSERT INTO t VALUES (5)`. -/
def insertFive : Syntax.Statement := .insert (name! "t") none [[.numeric "5"]] []

/-- {lit}`CREATE TABLE log(x)` and {lit}`CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO log VALUES (1); END`. -/
def logTrigger : List Syntax.Statement :=
  [.createTable (name! "log") [column (name! "x") none] [],
    .createTrigger (name! "r") false .after .insert (name! "t") none [.insert (name! "log") none [[.numeric "1"]] []]]

/-- The copy with a trigger on the target, for a source with the statements {lit}`source`. -/
def triggeredCopy (source : List Syntax.Statement) : List Syntax.Statement :=
  source ++ [createTarget] ++ logTrigger ++ [insertParameter, insertParameter, copySource (some positive)]

/-- {lit}`INSERT INTO t SELECT abs(x) FROM s WHERE x < 100 LIMIT 1`. -/
def insertAbsFirst : Syntax.Statement :=
  .insertSelect (name! "t") none
    { columns := [.expression (.call "abs" [.identifier (name! "x") .none]) none "abs"],
      source := some { table := name! "s", alias := none }, joins := [],
      filter := some (.compare .lt (.identifier (name! "x") .none) (.numeric "100")),
      groupBy := [], orderBy := [], limit := some (.numeric "1"), offset := none } []

/-- {lit}`SELECT id FROM t`. -/
def selectIds : Syntax.Statement :=
  .select [.expression (.identifier (name! "id") .none) none "id"] (some { table := name! "t", alias := none })
    [] none [] [] none none

/-- The script of an index on {lit}`s(x)` with the rows 5 and the smallest integer, and the copy of
the first row of {lit}`abs(x)` followed by a query of the target. -/
def limitedCopy : List Syntax.Statement :=
  indexedSource ++ [createIdTarget, insertParameter, insertParameter, insertAbsFirst, selectIds]

end Belay.Sqlite.Model.InsertSelectExamples
