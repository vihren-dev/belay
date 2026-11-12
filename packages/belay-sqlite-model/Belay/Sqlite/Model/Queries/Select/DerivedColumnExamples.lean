import Belay.Sqlite.Model.Queries.Select.CompoundResolutionExamples
import Belay.Sqlite.Model.Queries.Select.DerivedColumns

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.DerivedColumnExamples

open Syntax Resolution.CollationExamples Resolution.CompoundResolutionExamples

/-- A three-column source with TEXT, INTEGER and absent expression affinity. -/
def source : ScopeSource := derivedScopeSource 0 (some (name! "d"))
  [{ name := "a", affinity := some .text, collation := .nocase, types := (false, true) },
   { name := "b", affinity := some .integer, collation := .binary, types := (true, false) },
   { name := "c", affinity := none, collation := .binary, types := (true, false) }]

/-- Each column keeps its own affinity, including the absence of one on the third column. -/
example : ([0, 1, 2].map (Scope.affinityAt [source])) = [some .text, some .integer, none] := by decide +kernel

/-- Comparing a TEXT column with the literal-derived column applies TEXT affinity. -/
example : comparisonAffinity (Scope.affinityAt [source] 0) (Scope.affinityAt [source] 2) = some .text := by decide +kernel

/-- Only the first output column has NOCASE; the derived source has no implicit rowid. -/
example : (source.columns.map (·.collation), source.hasRowid) = ([.nocase, .binary, .binary], false) := by decide +kernel

/-- An anonymous query source cannot be named by a quoted empty qualifier. -/
example : (derivedScopeSource 0 none []).named (name! "") = false := by decide +kernel

/-- One expression's source column, used to check compound affinity combination. -/
def columnOf (expression : Expr) : DerivedColumn :=
  ((resultSourceColumns [] {} [shown expression] ["x"]).head?).getD
    { name := "x", affinity := none, collation := .binary, types := (false, false) }

/-- TEXT affinity degrades to BLOB when a different term is numeric. -/
example : compoundSourceAffinity [columnOf (num "1"), columnOf (.cast (.string [49]) "TEXT")] =
    some .blob := by decide +kernel

/-- Numeric affinity degrades to BLOB when a different term is text. -/
example : compoundSourceAffinity [columnOf (.string [49]), columnOf (.cast (num "1") "NUMERIC")] =
    some .blob := by decide +kernel

/-- A text literal and TEXT CAST retain TEXT affinity. -/
example : compoundSourceAffinity [columnOf (.string [49]), columnOf (.cast (.string [49]) "TEXT")] =
    some .text := by decide +kernel

/-- Unary plus removes affinity but keeps the CAST's numeric type possibilities. -/
example : let value := Expr.positive (.cast (num "1") "INTEGER")
    (value.sourceAffinity [] {}, value.sourceTypes [] {}) = (none, (true, false)) := by decide +kernel

/-- CASE combines only result arms; numeric conditions cannot make text results numeric. -/
example : (Expr.caseOf [num "1", .string [97], .string [98]] false).sourceTypes [] {} =
    (false, true) := by decide +kernel

/-- The ordering term that makes a non-UNION-ALL compound use derived-column metadata. -/
def rewrittenOrder : List OrderTerm := [ascending (.collate (num "1") (name! "BINARY"))]

/-- The scope of two TEXT columns merged by USING, with NOCASE only on the left. -/
def mergedScope (rule : MergeRule) : Scope :=
  [{ name := name! "a", columns := [{ name := name! "x", declaredType := some "TEXT", collation := .nocase }] },
   { name := name! "b", columns := [{ name := name! "x", declaredType := some "TEXT" }],
     offset := 1, merged := [0], mergeRule := rule }]

/-- A full-join output coalesces both columns, so the derived column has no affinity and
BINARY collation. This differs from the collation of the generated USING equality. -/
example : (resultSourceColumns (mergedScope .coalesce) {} [.star] ["x"]).map
    (fun column => (column.affinity, column.collation)) = [(none, .binary)] := by decide +kernel

/-- A right-join output reads the right column's affinity and BINARY collation. -/
example : (resultSourceColumns (mergedScope .takeRight) {} [.star] ["x"]).map
    (fun column => (column.affinity, column.collation)) = [(some .text, .binary)] := by decide +kernel

/-- A left-join output retains the left column's affinity and NOCASE collation. -/
example : (resultSourceColumns (mergedScope .keepLeft) {} [.star] ["x"]).map
    (fun column => (column.affinity, column.collation)) = [(some .text, .nocase)] := by decide +kernel

/-- Written merged names have the same output collation as their star expansion. -/
example : ((ref (name! "x")).columnCollation (mergedScope .coalesce),
    (ref (name! "x")).columnCollation (mergedScope .takeRight)) = (none, some .binary) := by decide +kernel

end Belay.Sqlite.Model.Resolution.DerivedColumnExamples
