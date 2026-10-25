import Belay
import Belay.Sqlite.SqlDocBindings

set_option doc.verso true

namespace SqlDocBindings
open Belay.Sqlite Belay.Sqlite.SqlDoc Belay.Sqlite.Translation

/-- The parameter tokens of each statement of a SQL text, from the real translation. -/
def parametersOf (text : String) : IO (List (List Parameter)) := do
  match ← translateText text with
  | .ok items => pure (items.toList.map (·.parameters))
  | .error refusal => throw (IO.userError refusal.message)

/-- Fail with the label when the condition is false. -/
def expect (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"binding check failed: {label}")

/-- The places of the problems of a result, or none for a success. -/
def places (result : Except (List Problem) ParameterPlan) : List Place :=
  match result with
  | .ok _ => []
  | .error problems => problems.map (·.place)

/-- Whether a result is a failure whose first message contains the text. -/
def failsWith (result : Except (List Problem) ParameterPlan) (text : String) : Bool :=
  match result with
  | .error (problem :: _) => (problem.message.splitOn text).length > 1
  | _ => false

#eval show IO Unit from do
  -- First appearance, numbering and sparse slots: :a is 1, ?3 is 3, @b is 4, and number 2 is NULL.
  let statements ← parametersOf "SELECT :a, ?3, @b, :a"
  let .ok plan := namedPlan statements ["a", "p3", "b"] | throw (IO.userError "plan expected")
  let lookup : String → Option Value := fun name => some (.text name.toUTF8.toList)
  expect "slots" (planValues plan lookup == [[.text "a".toUTF8.toList, .null, .text "p3".toUTF8.toList, .text "b".toUTF8.toList]])
  -- A $ name is a header name in a documentation block, with no capture of a Lean variable.
  let dollar ← parametersOf "SELECT $x"
  expect "dollar" (places (namedPlan dollar ["x"]) == [])
  expect "dollar missing" (places (namedPlan dollar []) == [.sql 7 9])
  -- Missing parameters are at their token; unused arguments are at the header.
  let missing ← parametersOf "SELECT :a; SELECT @b"
  expect "missing" (places (namedPlan missing ["a"]) == [.sql 18 20])
  expect "unused" (places (namedPlan missing ["a", "b", "z"]) == [.header "z"])
  -- Reserved names and names that no header argument can have.
  let reserved ← parametersOf "SELECT :db, :values, ?1"
  expect "reserved" (places (namedPlan reserved ["p1"]) == [.sql 7 10, .sql 12 19])
  let odd ← parametersOf "SELECT $a::b"
  expect "odd name" (failsWith (namedPlan odd []) "(values := ...)")
  -- Different signs are different SQLite parameters but one Lean name.
  let signs ← parametersOf "SELECT :x, @x"
  expect "signs" (failsWith (namedPlan signs ["x"]) "both give the Lean name x")
  -- Explicit lists: one list per statement and one value per number up to the largest.
  let explicit ← parametersOf "SELECT :x, @x; SELECT 1; SELECT ?3"
  expect "explicit ok" (explicitProblems explicit [[1, 2], [], [.null, .null, 3]] == [])
  expect "explicit statements" ((explicitProblems explicit [[1, 2]]).map (·.place) == [.header "values"])
  expect "explicit short" ((explicitProblems explicit [[1], [], [.null, .null, 3]]).length == 1)
  expect "explicit long" ((explicitProblems explicit [[1, 2], [3], [.null, .null, 3]]).length == 1)
  expect "explicit sparse short" ((explicitProblems explicit [[1, 2], [], [3]]).length == 1)

end SqlDocBindings

open Lean Elab Command in
run_cmd logInfo "SQL doc binding checks passed"
