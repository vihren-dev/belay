import Belay.Sqlite.Model.Resolution.Values
import Belay.Sqlite.Model.Resolution.MergedNames
import Belay.Sqlite.Model.Resolution.FunctionCalls
import Belay.Sqlite.Model.Resolution.SyntaxScope
import Belay.Sqlite.Model.ExprEval
import Belay.Sqlite.Model.Resolution.ExprAny
import Belay.Sqlite.Model.ClockReads
import Belay.Sqlite.Model.Resolution.Collations
import Belay.Sqlite.Model.Resolution.SubqueryShapes

import Belay.Sqlite.Model.Resolution.OperandRecords
import Belay.Sqlite.Model.Resolution.TracedIssues

set_option doc.verso true

/-! The arms of the traced operand resolution that need no recursion: a name over a scope, and the
comparisons that read the operands already resolved. Each records the decision it makes and
returns the value that follows from the same decision. -/

namespace Belay.Sqlite.Model

/-- The name that an error message gives for the column {lit}`schema.source.column`, or
{lit}`source.column` without a schema, as SQLite writes it. -/
def qualifiedName (schema : Option Identifier) (source column : Identifier) : Identifier :=
  ⟨(schema.map (·.bytes ++ [46])).getD [] ++ source.bytes ++ [46] ++ column.bytes⟩

/-- The operand of an unqualified column name over a scope, with its occurrence: the name of the
columns that {name}`Scope.resolveName` finds, the error or the fallback that {name}`missingUse`
chooses for a name no column has, or {lit}`ambiguous column name`. A name that no column has lists
{lit}`aliases` after the columns as candidates, for a place where a result alias is legal. -/
def identifierTraced (dqs : Bool) (scope : Scope) (name : Identifier) (quote : Syntax.QuoteKind)
    (aliases : List Candidate := []) : Traced ValueIssue Operand :=
  match scope.resolveName name with
  | .found _ reads => do
    Traced.record (Scope.identifierOccurrence name quote (.found (scope.bindingsAt reads)))
    Traced.lift (scope.nameRead reads)
  | .missing => do
    let use := missingUse dqs scope name quote
    Traced.record (Scope.identifierOccurrence name quote (.missing use (scope.columnCandidates ++ aliases)))
    match use with
    | .rowidName => throw (.restriction [] .rowidName)
    | .textLiteral => pure (.literal (.text name.bytes), none)
    | .booleanKeyword => pure (.literal (.integer (if name.isKeyword (bytes! "true") then 1 else 0)), none)
    | .error => throw (.prepare (.noSuchColumn name))
  | .ambiguous => do
    Traced.record (Scope.identifierOccurrence name quote (.ambiguous (scope.ambiguousCandidates name)))
    throw (.prepare (.ambiguousColumn name))

/-- The operand of a qualified column name over a scope, with the occurrences of its schema, its
source and its column. The source is recorded as the resolver selected it. -/
def qualifiedTraced (scope : Scope) (source column : Identifier) (schema : Option Identifier) :
    Traced ValueIssue Operand :=
  match scope.resolveSchemaQualified source column schema with
  | .found _ reads => do
    let bindings := scope.bindingsAt reads
    Traced.recordAll (scope.qualifierOccurrences source schema (bindings.head?.map (·.source)))
    Traced.record (Scope.columnOccurrence column (.found bindings))
    Traced.lift (scope.nameRead reads)
  | .missing => do
    let use := if rowidName column && scope.rowidSource source then MissingUse.rowidName else .error
    Traced.recordAll (scope.qualifierOccurrences source schema none)
    Traced.record (Scope.columnOccurrence column (.missing use (scope.qualifiedCandidates source schema)))
    match use with
    | .rowidName => throw (.restriction [] .rowidName)
    | .error | .textLiteral | .booleanKeyword => throw (.prepare (.noSuchColumn (qualifiedName schema source column)))
  | .ambiguous => do
    let candidates := scope.ambiguousCandidates column (some source) schema
    let chosen := match candidates with
      | .column binding :: _ => some binding.source
      | .resultAlias .. :: _ | .source _ :: _ | [] => none
    Traced.recordAll (scope.qualifierOccurrences source schema chosen)
    Traced.record (Scope.columnOccurrence column (.ambiguous candidates))
    throw (.prepare (.ambiguousColumn (qualifiedName schema source column)))

/-- The comparison of two resolved operands: a truth test such as {lit}`x IS TRUE`
({name}`truthTest`) applies no affinity and the binary collation; any other comparison applies
{name}`comparisonAffinity` and {name}`comparisonCollation`. The comparison is recorded. -/
def compareTraced (scope : Scope) (operator : Comparison) (left right : Syntax.Expr) (a b : Operand) :
    Traced ValueIssue Operand :=
  if truthTest operator right b.1 then do
    -- x IS [NOT] TRUE is (NOT NOT x) IS [NOT] 1, and x IS [NOT] FALSE is (NOT x) IS [NOT] 1.
    let tested := if b.1.literal? == some (.integer 1) then .not (.not a.1) else .not a.1
    Traced.record (comparisonOccurrence (.operator operator) none .binary)
    pure (.compare operator none tested (.literal (.integer 1)), none)
  else do
    let affinity := comparisonAffinity a.2 b.2
    let collation := comparisonCollation scope left right
    Traced.record (comparisonOccurrence (.operator operator) affinity collation)
    pure (.compare operator affinity a.1 b.1 collation, none)

/-- {lit}`x IN (list)` over the resolved operand and list: it compares under the affinity and the
collation of {lit}`x`, but a list of one constant value with an explicit collation is
{lit}`x = +c`, as SQLite's parser reads it. The comparison is recorded. -/
def inListTraced (scope : Scope) (shapes : SubqueryShapes) (operand : Syntax.Expr) (values : List Syntax.Expr)
    (negated : Bool) (a : Operand) (resolved : Resolved.Arguments) : Traced ValueIssue Operand :=
  match values, resolved with
  | [value], .cons element .nil =>
    if value.explicitCollation.isSome && (element.lowestRead shapes).isNone &&
        !element.any Resolved.Expr.namesSubquery && !element.readsClock then do
      let collation := comparisonCollation scope operand value
      Traced.record (comparisonOccurrence .inList a.2 collation)
      let compared := .compare .eq a.2 a.1 element collation
      pure (if negated then .not compared else compared, none)
    else do
      Traced.record (comparisonOccurrence .inList a.2 (operand.collationIn scope))
      pure (.inList a.1 resolved a.2 (operand.collationIn scope) negated, none)
  | _, _ => do
    Traced.record (comparisonOccurrence .inList a.2 (operand.collationIn scope))
    pure (.inList a.1 resolved a.2 (operand.collationIn scope) negated, none)

/-- {lit}`x BETWEEN a AND b` over the resolved operands is {lit}`x >= a AND x <= b`. The two
comparisons are recorded. -/
def betweenTraced (scope : Scope) (operand low high : Syntax.Expr) (negated : Bool) (a l h : Operand) :
    Traced ValueIssue Operand := do
  let lowAffinity := comparisonAffinity a.2 l.2
  let lowCollation := comparisonCollation scope operand low
  let highAffinity := comparisonAffinity a.2 h.2
  let highCollation := comparisonCollation scope operand high
  Traced.record (comparisonOccurrence .betweenLow lowAffinity lowCollation)
  Traced.record (comparisonOccurrence .betweenHigh highAffinity highCollation)
  let both := Resolved.Expr.and (.compare .ge lowAffinity a.1 l.1 lowCollation)
    (.compare .le highAffinity a.1 h.1 highCollation)
  pure (if negated then .not both else both, none)

/-- {lit}`x IN (q)` over the resolved operand and the shape of the query's column: it compares under
{name}`comparisonAffinity` and {name}`inCollation`, which are recorded. -/
def inQueryTraced (scope : Scope) (operand : Syntax.Expr) (index : Nat) (negated : Bool) (a : Operand)
    (shape : SubqueryShape) : Traced ValueIssue Operand := do
  let affinity := comparisonAffinity a.2 shape.affinity
  let collation := inCollation scope operand shape
  Traced.record (comparisonOccurrence .inQuery affinity collation)
  pure (.inQuery a.1 index affinity collation negated, none)

/-- The {lit}`iif` argument for a {lit}`WHEN` value of a {lit}`CASE` with a base value: the
comparison of the base and the value as {lit}`=` compares them, recorded at {lit}`path`. -/
def caseWhenTraced (scope : Scope) (path : List Nat) (written : Syntax.Expr) (value : Operand)
    (operand : Syntax.Expr) (resolved : Operand) : Traced ValueIssue Resolved.Expr := do
  let affinity := comparisonAffinity value.2 resolved.2
  let collation := comparisonCollation scope written operand
  Traced.record { comparisonOccurrence .caseWhen affinity collation with path }
  pure (.compare .eq affinity value.1 resolved.1 collation)

end Belay.Sqlite.Model
