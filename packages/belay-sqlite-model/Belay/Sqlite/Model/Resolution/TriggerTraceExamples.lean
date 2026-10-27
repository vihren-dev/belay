import Belay.Sqlite.Model.Resolution.Examples
import Belay.Sqlite.Model.Resolution.TriggerPrograms

set_option doc.verso true

/-! Examples of the trace of a trigger's program (ADR 0018, D5), checked by {lit}`#guard` when the
package builds: the names of the {lit}`WHEN` condition and of each statement of the body are
recorded at their paths in the trigger as written, the condition below the child 5 and the
statement {lit}`k` below {lit}`[6, k]`. A rename of a table or a column reads these paths. -/

namespace Belay.Sqlite.Model.Resolution.TriggerTraceExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The tables {lit}`t(a, b)` and {lit}`log(x)`. -/
def tables : Catalog := catalogOf (schema [
  .createTable (name! "t") [column (name! "a"), column (name! "b")] [],
  .createTable (name! "log") [column (name! "x")] []])

/-- {lit}`source.name`. -/
def dotted (source name : String) : Expr := .qualified (Identifier.ofString source) (Identifier.ofString name)

/-- {lit}`AFTER UPDATE OF a ON t WHEN new.a > old.a BEGIN UPDATE log SET x = new.b WHERE x = old.a;
INSERT INTO log(x) VALUES (new.a); SELECT a FROM t WHERE b = new.b; END`. -/
def trigger : CatalogTrigger where
  table := name! "t"
  time := .after
  event := .update [name! "a"]
  condition := some (.compare .gt (dotted "new" "a") (dotted "old" "a"))
  body := [
    .update (name! "log") [(name! "x", dotted "new" "b")]
      (some (.compare .eq (.identifier (name! "x") .none) (dotted "old" "a"))),
    .insert (name! "log") (some [name! "x"]) [[dotted "new" "a"]] [],
    .select [.expression (.identifier (name! "a") .none) none "a"] (some { table := name! "t", alias := none }) []
      (some (.compare .eq (.identifier (name! "b") .none) (dotted "new" "b"))) [] [] none none]

/-- The paths and names of the trace of the program of the trigger. -/
def occurrences : List (List Nat × Option Identifier) :=
  ((resolveProgramTraced { profile := defaults, mode := .execution } tables 2 trigger).trace).map
    fun occurrence => (occurrence.path, occurrence.name)

/-- The paths and names of the occurrences that have a name. -/
def named : List (List Nat × String) :=
  occurrences.filterMap fun ((path, name) : List Nat × Option Identifier) => name.map fun name => (path, name.text)

-- The condition is the child 5; the statements are the children 0, 1 and 2 of the child 6.
#guard named.take 4 == [([5, 1, 0], "new"), ([5, 1, 1], "a"), ([5, 2, 0], "old"), ([5, 2, 1], "a")]
-- UPDATE log SET x = new.b WHERE x = old.a: the table, the value, the assignment target and the filter.
#guard (named.filter (·.1.take 2 == [6, 0])).map Prod.snd == ["log", "new", "b", "x", "x", "old", "a"]
#guard named.contains ([6, 0, 0], "log") && named.contains ([6, 0, 1, 0, 0], "x") && named.contains ([6, 0, 2, 1], "x")
-- INSERT INTO log(x) VALUES (new.a): the table, the column of the list and the cells of the row.
#guard (named.filter (·.1.take 2 == [6, 1])) ==
  [([6, 1, 0], "log"), ([6, 1, 1, 0], "x"), ([6, 1, 2, 0, 0, 0], "new"), ([6, 1, 2, 0, 0, 1], "a")]
-- SELECT a FROM t WHERE b = new.b: the source, the column of the result and those of the filter.
#guard (named.filter (·.1.take 2 == [6, 2])) ==
  [([6, 2, 1, 0], "t"), ([6, 2, 0, 0, 0], "a"), ([6, 2, 3, 1], "b"), ([6, 2, 3, 2, 0], "new"), ([6, 2, 3, 2, 1], "b")]

/-- {lit}`BEFORE INSERT ON t BEGIN SELECT CASE WHEN new.a < 0 THEN RAISE(ABORT, 'no') END; END`. -/
def raising : CatalogTrigger where
  table := name! "t"
  time := .before
  event := .insert
  body := [.select [.expression (.caseOf [.compare .lt (dotted "new" "a") (.numeric "0"),
    .raise .abort (some (.string "no".toUTF8.toList))] false) none ""] none [] none [] [] none none]

-- The CASE of a raising SELECT keeps its operands in their places, so that the names of the condition
-- are at their written paths: the operand 0 of the list of operands (child 0) of the CASE.
#guard ((resolveProgramTraced { profile := defaults, mode := .execution } tables 2 raising).trace.filterMap
    fun occurrence => occurrence.name.map fun name => (occurrence.path, name.text)) ==
  [([6, 0, 0, 0, 0, 0, 0, 1, 0], "new"), ([6, 0, 0, 0, 0, 0, 0, 1, 1], "a")]

/-- {lit}`BEFORE INSERT ON t BEGIN SELECT CASE WHEN 1 THEN RAISE(ABORT, new.b) END; END`. -/
def raisingWithName : CatalogTrigger where
  table := name! "t"
  time := .before
  event := .insert
  body := [.select [.expression (.caseOf [.numeric "1", .raise .abort (some (dotted "new" "b"))] false) none ""] none []
    none [] [] none none]

-- The message is a result column of the SELECT that is resolved; its names move to the message in the written
-- CASE: the operand 1 of the CASE, then the child 1 of the RAISE.
#guard ((resolveProgramTraced { profile := defaults, mode := .execution } tables 2 raisingWithName).trace.filterMap
    fun occurrence => occurrence.name.map fun name => (occurrence.path, name.text)) ==
  [([6, 0, 0, 0, 0, 0, 1, 1, 0], "new"), ([6, 0, 0, 0, 0, 0, 1, 1, 1], "b")]

end Belay.Sqlite.Model.Resolution.TriggerTraceExamples
