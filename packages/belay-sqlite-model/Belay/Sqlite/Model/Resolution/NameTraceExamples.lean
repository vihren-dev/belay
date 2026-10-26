import Belay.Sqlite.Model.Resolution.OperandTraced

set_option doc.verso true

/-! Examples of the name trace of expressions: what the traced operand resolution records for a
found, a missing, an ambiguous and a qualified name, for the double-quoted fallback, for a name of
an enclosing query and for a comparison. Each example checks the occurrences of the trace, and
that the projection of the traced resolution gives the same result. -/

namespace Belay.Sqlite.Model.NameTraceExamples

/-- A column with a name and a declared type. -/
private def column (text declaredType : String) : CatalogColumn :=
  { name := Identifier.ofString text, declaredType := some declaredType }

/-- The identifier of a text. -/
private def name (text : String) : Identifier := Identifier.ofString text

/-- A source of a scope with a name and columns, at depth 0. -/
private def sourceOf (text : String) (columns : List CatalogColumn) : ScopeSource :=
  { name := name text, columns }

/-- One table {lit}`t(a INTEGER, b TEXT)`. -/
private def tableT : Scope := Scope.place [sourceOf "t" [column "a" "INTEGER", column "b" "TEXT"]]

/-- Two tables, {lit}`t(a INTEGER, b TEXT)` and {lit}`u(b TEXT, c NUMERIC)`: {lit}`b` is in both. -/
private def tablesTU : Scope :=
  Scope.place [sourceOf "t" [column "a" "INTEGER", column "b" "TEXT"],
    sourceOf "u" [column "b" "TEXT", column "c" "NUMERIC"]]

/-- The traced resolution of an expression over a scope, without shapes and with aggregates as misuse. -/
private def traced (dqs : Bool) (scope : Scope) (expr : Syntax.Expr) :=
  resolveOperandTraced dqs scope {} true expr

/-- An unqualified column name with a quote kind. -/
private def identifier (text : String) (quote : Syntax.QuoteKind := .none) : Syntax.Expr :=
  .identifier (name text) quote

/-- The result of the one occurrence of a trace that has one. -/
private def onlyResult (trace : NameTrace) : Option NameResult :=
  match trace with
  | [occurrence] => some occurrence.result
  | _ => none

/-- A found name records the binding of its column, with the declared affinity. -/
private def foundNameIsBound : Bool := (match onlyResult (traced true tableT (identifier "A")).trace with
    | some (.found [binding]) =>
      binding.source.name == name "t" && binding.source.index == 0 && binding.source.depth == 0 &&
      binding.column.name == name "a" && binding.column.position == 0 &&
      binding.column.affinity == some .integer
    | _ => false)

#guard foundNameIsBound

/-- A name that no column has is missing, with all columns as candidates, and the traced resolution
fails as {lit}`no such column`. -/
private def missingNameFails : Bool := (match (traced true tableT (identifier "z")).trace, (traced true tableT (identifier "z")).drop with
    | [occurrence], .error (.prepare (.noSuchColumn missing)) =>
      missing == name "z" && occurrence.exact && occurrence.path == [] &&
      (match occurrence.result with
        | .missing .error candidates => candidates.length == 2
        | _ => false)
    | _, _ => false)

#guard missingNameFails

/-- A double-quoted name that no column has is a text literal when the fallback is on, and is
missing when it is off. -/
private def doubleQuotedFallback : Bool := (match onlyResult (traced true tableT (identifier "z" .double)).trace,
      onlyResult (traced false tableT (identifier "z" .double)).trace with
    | some (.missing .textLiteral _), some (.missing .error _) => true
    | _, _ => false)

#guard doubleQuotedFallback

/-- A name of both tables is ambiguous with the column of each table as candidate. -/
private def ambiguousNameHasBothCandidates : Bool := (match onlyResult (traced true tablesTU (identifier "b")).trace with
    | some (.ambiguous candidates) => candidates.length == 2
    | _ => false)

#guard ambiguousNameHasBothCandidates

/-- A name of the second table only is found in the source with index 1. -/
private def secondTableSourceIndex : Bool := (match onlyResult (traced true tablesTU (identifier "c")).trace with
    | some (.found [binding]) => binding.source.index == 1 && binding.column.position == 3
    | _ => false)

#guard secondTableSourceIndex

/-- A qualified name records the source part at part 0 and the column part at part 1. -/
private def qualifiedNameParts : Bool := (match (traced true tablesTU (.qualified (name "u") (name "b"))).trace with
    | [source, column] =>
      source.path == [0] && source.role == .qualifier &&
      (match source.result with
        | .source reference => reference.index == 1 && reference.name == name "u"
        | _ => false) &&
      column.path == [1] && column.role == .columnReference &&
      (match column.result with
        | .found [binding] => binding.column.position == 2
        | _ => false)
    | _ => false)

#guard qualifiedNameParts

/-- A qualified name whose qualifier names a source of the query and one of the query around it takes
the qualifier from the nearer source, as the column does. -/
private def qualifierShadowing : Bool :=
  (match (traced true (Scope.enclose tableT (Scope.place [sourceOf "t" [column "a" "TEXT"]] 2))
      (.qualified (name "t") (name "a"))).trace with
    | [source, column] =>
      (match source.result, column.result with
        | .source reference, .found [binding] =>
          reference.depth == 0 && binding.source.depth == 0 && binding.column.affinity == some .text
        | _, _ => false)
    | _ => false)

#guard qualifierShadowing

/-- A name that only the enclosing query has is found at depth 1, and the source keeps its index in
the enclosing query. -/
private def enclosingQueryDepth : Bool := (match onlyResult (traced true (Scope.enclose tablesTU (Scope.place [sourceOf "v" [column "d" ""]] 4))
      (identifier "c")).trace with
    | some (.found [binding]) => binding.source.depth == 1 && binding.source.index == 1
    | _ => false)

#guard enclosingQueryDepth

/-- A comparison records the affinity and the collation it applied, after the occurrences of its
operands. -/
private def comparisonRecordsAffinity : Bool := (match (traced true tableT (.compare .eq (identifier "a") (identifier "b"))).trace with
    | [_, _, comparison] =>
      comparison.role == .comparisonSite &&
      (match comparison.result with
        | .compared (.operator .eq) affinity collation => affinity == some .numeric && collation == .binary
        | _ => false)
    | _ => false)

#guard comparisonRecordsAffinity

/-- An ambiguous operand of a comparison stops the resolution: the trace holds the occurrences up to
and including that name, and no comparison. -/
private def failureStopsTrace : Bool := (match (traced true tablesTU (.compare .eq (identifier "a") (identifier "b"))).trace with
    | [_, ambiguous] => (match ambiguous.result with | .ambiguous _ => true | _ => false)
    | _ => false)

#guard failureStopsTrace

end Belay.Sqlite.Model.NameTraceExamples
