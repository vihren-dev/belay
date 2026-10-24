import Belay.Sqlite.Model.Resolution.ColumnOriginExamples

set_option doc.verso true

/-! Kernel checks of normalized source declarations. These cover the distinct
left and right compound origins and propagation of SQLite's FLEXNUM metadata,
which view column descriptions require even when expression affinity agrees. -/

namespace Belay.Sqlite.Model.Resolution.ColumnTypeExamples

open Syntax Resolution.Examples Resolution.DerivedColumnExamples
  Resolution.ColumnOriginExamples Resolution.CollationExamples

/-- A direct physical column retains its declaration; untyped columns have
BLOB affinity and get the normalized declaration BLOB. -/
example : (resultSourceColumns typedScope {} [.star] ["s", "i", "r", "u"]).map (·.declaredType) =
    [some "VARCHAR(20)", some "INTEGER", some "REAL", some "BLOB"] := by decide +kernel

/-- A CAST gets a canonical type name, COLLATE retains affinity but loses the
origin spelling, and unary plus has no affinity or normalized declaration. -/
example : (columnsOf [.cast (ref (name! "i")) "INTEGER",
    .collate (ref (name! "s")) (name! "NOCASE"), .positive (ref (name! "i"))]).map (·.declaredType) =
    [some "INT", some "TEXT", none] := by decide +kernel

/-- Direct compound metadata starts with the left INTEGER declaration. -/
example : mixedNumeric.map (fun column => (column.declaredType, column.originType)) =
    [(some "INTEGER", some "REAL")] := by decide +kernel

/-- Reading the compound follows its right REAL origin but its INTEGER
affinity, so the next source gets the canonical INT declaration. -/
example : (resultSourceColumns [derivedScopeSource 0 (some (name! "d")) mixedNumeric] {}
    [shown (ref (name! "x"))] ["x"]).map (fun column => (column.declaredType, column.originType)) =
      [(some "INT", some "REAL")] := by decide +kernel

/-- A numeric column and a numeric declaration spelled NUM. -/
def numericScope : Scope := Scope.single (name! "n")
  [{ name := name! "n", declaredType := some "NUMERIC" },
   { name := name! "m", declaredType := some "NUM" }]

/-- Metadata for one expression over the two numeric columns. -/
def numericColumn (value : Expr) : List DerivedColumn :=
  resultSourceColumns numericScope {} [shown value] ["x"]

/-- A compound whose first CAST gives FLEXNUM metadata. -/
def flexibleColumns : List DerivedColumn := compoundSourceColumns
  [numericColumn (.cast (ref (name! "n")) "INTEGER"), numericColumn (ref (name! "n"))]

/-- A compound with ordinary NUMERIC metadata and the same NUM declaration. -/
def ordinaryColumns : List DerivedColumn := compoundSourceColumns
  [numericColumn (ref (name! "m")), numericColumn (ref (name! "n"))]

/-- Read the supplied query source once more. -/
def nestedColumns (columns : List DerivedColumn) : List DerivedColumn :=
  resultSourceColumns [derivedScopeSource 0 (some (name! "d")) columns] {} [shown (ref (name! "x"))] ["x"]

/-- The equal declarations do not erase the FLEXNUM distinction. An enclosing
derived query retains NUM for FLEXNUM and NUMERIC for ordinary affinity. -/
example : [flexibleColumns, ordinaryColumns, nestedColumns flexibleColumns, nestedColumns ordinaryColumns].map
    (fun columns => columns.map fun column => (column.declaredType, column.flexibleNumeric)) =
      [[(some "NUM", true)], [(some "NUM", false)], [(some "NUM", true)], [(some "NUMERIC", false)]] :=
  by decide +kernel

/-- A text possibility changes numeric compound affinity to BLOB, which also
clears FLEXNUM metadata. -/
example : (compoundSourceColumns [flexibleColumns, columnsOf [ref (name! "s")]]).map
    (fun column => (column.affinity, column.declaredType, column.flexibleNumeric)) =
      [(some .blob, some "BLOB", false)] := by decide +kernel

/-- A star uses the selected source cell's FLEXNUM metadata. -/
example : resultFlexibleNumerics [derivedScopeSource 0 none flexibleColumns] {} [.star] = [true] :=
  by decide +kernel

/-- A scalar subquery and COLLATE inherit FLEXNUM; a new CAST and unary plus
do not retain that flag. -/
example : let shapes : SubqueryShapes :=
    { later := [{ parent := none, columns := 1, affinity := some .numeric,
                  flexibleNumeric := true, explicitCollation := none,
                  columnCollation := none, lowest := none }] }
    [Expr.subquery 0, .collate (.subquery 0) (name! "NOCASE"), .cast (.subquery 0) "NUMERIC",
      .positive (.subquery 0)].map (·.flexibleNumeric [] shapes) = [true, true, false, false] := by decide +kernel

end Belay.Sqlite.Model.Resolution.ColumnTypeExamples
