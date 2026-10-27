import Belay.Sqlite.Model.Resolution.DerivedResolutionExamples

set_option doc.verso true

/-! Kernel checks of ordinary CTE syntax through resolution and the shared evaluator.
The public and native suites check the SQL spellings; these examples also cover raw syntax
and a caller-supplied parameter, clock and counter context. -/

namespace Belay.Sqlite.Model.Resolution.CommonTableResolutionExamples

open Syntax Resolution.Examples Resolution.CollationExamples Resolution.CompoundResolutionExamples

/-- Mark a query as a WITH definition in its existing parent scope. -/
def definition (name : String) (body : Subquery) (columns : Option (List String) := none) : Subquery :=
  { body with commonTable := some {
      name := Identifier.ofString name
      columns := columns.map (List.map Identifier.ofString) } }

/-- Read a named CTE through the ordinary source syntax. -/
def fromName (name : String) (queries : List Subquery) : Syntax.Statement :=
  .select [.star] (some { table := Identifier.ofString name, alias := none }) [] none [] [] none none queries

/-- A forward CTE reference expands before the containing query resolves its columns. -/
example : rowsOf (fromName "a" [definition "a" (term [.star] "b"),
    definition "b" (term [named (num "3") "x"])]) = some [[.integer 3]] := by decide +kernel

/-- Duplicate explicit output names use SQLite's derived-column suffixes. -/
example : namesOf (fromName "a" [definition "a" (term [shown (num "1"), shown (num "2")])
    (some ["x", "x"])]) = some ["x", "x:1"] := by decide +kernel

/-- Duplicate names in the same WITH list fail even for direct syntax callers. -/
example : errorOf (fromName "a" [definition "a" (term [shown (num "1")]),
    definition "A" (term [shown (num "2")])]) =
      some (.expression (.commonTable (.duplicate (name! "A")))) := by decide +kernel

/-- A circular ordinary CTE reports a preparation error rather than an empty result. -/
example : errorOf (fromName "a" [definition "a" (term [.star] "a")]) =
    some (.expression (.commonTable (.circular (name! "a")))) := by decide +kernel

/-- Explicit names are counted only when the definition is used. -/
example : errorOf (fromName "a" [definition "a" (term [shown (num "1")]) (some ["x", "y"])]) =
    some (.expression (.commonTable (.columns (name! "a") 1 2))) := by decide +kernel

/-- Resolve a statement and read its rows with the given statement context. -/
def rowsInContext (statement : Syntax.Statement) (clock : Int) (counters : Counters)
    (parameters : List Value) : Option (List (List Value)) :=
  match resolvedOne statement with
  | some (.query query subqueries) =>
    (query.runOn clock counters parameters CompoundResolutionExamples.tables.emptyDatabase subqueries).map (·.2.rows)
  | none => none
  | some (.createTable _ _ _) | some (.createView _ _ _) | some (.createIndex _ _ _) | some (.createTrigger _ _ _)
  | some (.addColumn _ _ _) | some (.rewrite _) | some (.drop _ _) | some .begin | some .commit | some .rollback
  | some (.insert _ _ _ _ _) | some (.update _ _ _ _ _ _)
  | some (.upsert _ _ _ _ _ _ _) | some (.insertSelect _ _ _ _ _ _ _ _) | some (.delete _ _ _ _ _)
  | some (.prepareError _) | some (.setting _ _) => none

/-- CTE copies share the parameter slots, supplied clock and connection counters of their use. -/
example : rowsInContext (fromName "c" [definition "c"
    (term [named (.parameter 1) "p", named (.call "changes" []) "n", named (.currentTime "CURRENT_DATE") "d"])])
    212640249600000 { changes := some 8 } [.integer 5] =
      some [[.integer 5, .integer 8, TimeKeyword.date.value 212640249600000]] := by decide +kernel

end Belay.Sqlite.Model.Resolution.CommonTableResolutionExamples
