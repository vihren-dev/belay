import Belay.Sqlite.Model.Resolution.DerivedColumnExamples

set_option doc.verso true

/-! Kernel checks of SQLite's declared-type origins. These examples distinguish
column declarations from expression affinity, follow the right-most compound
term, and check the origins of stars and scalar subqueries through resolution. -/

namespace Belay.Sqlite.Model.Resolution.ColumnOriginExamples

open Syntax Resolution.Examples Resolution.DerivedColumnExamples
  Resolution.CollationExamples Resolution.CompoundResolutionExamples

/-- Columns with distinct declared spellings and one untyped column. -/
def typedScope : Scope := Scope.single (name! "t")
  [{ name := name! "s", declaredType := some "VARCHAR(20)" },
   { name := name! "i", declaredType := some "INTEGER" },
   { name := name! "r", declaredType := some "REAL" },
   { name := name! "u", declaredType := none }]

/-- Source metadata for expressions over the declared columns. -/
def columnsOf (values : List Expr) : List DerivedColumn :=
  resultSourceColumns typedScope {} (values.map shown) (values.map fun _ => "x")

/-- Every star-expanded column retains its declared spelling, including the
absence of a declaration on the fourth column. -/
example : (resultSourceColumns typedScope {} [.star] ["s", "i", "r", "u"]).map (·.originType) =
    [some "VARCHAR(20)", some "INTEGER", some "REAL", none] := by decide +kernel

/-- COLLATE, CAST and unary plus have no column origin, even when their
affinities or collations come from an operand. -/
example : (columnsOf [.collate (ref (name! "s")) (name! "NOCASE"),
    .cast (ref (name! "i")) "INTEGER", .positive (ref (name! "i"))]).map (·.originType) =
    [none, none, none] := by decide +kernel

/-- Metadata of an INTEGER/REAL compound. -/
def mixedNumeric : List DerivedColumn := compoundSourceColumns
  [columnsOf [ref (name! "i")], columnsOf [ref (name! "r")]]

/-- The compound keeps INTEGER source affinity and follows the right REAL
origin. Those are independent pieces of column metadata. -/
example : mixedNumeric.map (fun column => (column.affinity, column.originType)) =
    [(some .integer, some "REAL")] := by decide +kernel

/-- A query reading the compound keeps its REAL origin. -/
example : (resultSourceColumns [derivedScopeSource 0 (some (name! "d")) mixedNumeric] {}
    [shown (ref (name! "x"))] ["x"]).map (·.originType) = [some "REAL"] := by decide +kernel

/-- FULL JOIN's merged star is a coalesce, so it has no origin declaration. -/
example : resultOriginTypes (mergedScope .coalesce) {} [.star] = [none] := by decide +kernel

/-- Merged columns with distinguishable declarations, for the outer-join rules. -/
def joinedOrigins (rule : MergeRule) : Scope :=
  [{ name := name! "a", columns := [{ name := name! "x", declaredType := some "INTEGER" }] },
   { name := name! "b", columns := [{ name := name! "x", declaredType := some "TEXT" }],
     offset := 1, merged := [0], mergeRule := rule }]

/-- LEFT JOIN retains the left declaration; RIGHT JOIN selects the right one.
The written merged name and the star expansion choose the same origin. -/
example : ([MergeRule.keepLeft, .takeRight].map fun rule =>
    ((ref (name! "x")).originType (joinedOrigins rule) {},
      resultOriginTypes (joinedOrigins rule) {} [.star])) =
      [(some "INTEGER", [some "INTEGER"]), (some "TEXT", [some "TEXT"])] := by decide +kernel

/-- A scalar shape with a REAL origin. -/
def scalarShapes : SubqueryShapes :=
  { later := [{ parent := none, columns := 1, affinity := some .real, originType := some "REAL",
                explicitCollation := none, columnCollation := none, lowest := none }] }

/-- A scalar result retains the supplied origin. -/
example : (Expr.subquery 0).originType [] scalarShapes = some "REAL" := by decide +kernel

/-- The catalog used to check the complete indexed subquery resolver. -/
def typedCatalog : Catalog :=
  [{ name := name! "t", entry := .table { columns := typedScope.columns } }]

/-- Resolution retains the right-most REAL origin of the compound, while
keeping the INTEGER and REAL origins on its two terms. -/
example : (resolveSubqueries true typedCatalog 8 (QueryScope.ofScope [])
    [{ commonTablePlaceholder with compound := some { first := 1, rest := [(.unionAll, 2)] } },
     { commonTablePlaceholder with
       columns := [shown (ref (name! "i"))]
       source := some { table := name! "t", alias := none }, parent := some 0 },
     { commonTablePlaceholder with
       columns := [shown (ref (name! "r"))]
       source := some { table := name! "t", alias := none }, parent := some 0 }]).toOption.map
    (fun (_, shapes) => shapes.map (·.originType)) =
      some [some "REAL", some "INTEGER", some "REAL"] := by decide +kernel

end Belay.Sqlite.Model.Resolution.ColumnOriginExamples
