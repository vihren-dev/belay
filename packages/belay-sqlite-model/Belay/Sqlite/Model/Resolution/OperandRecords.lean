import Belay.Sqlite.Model.Resolution.ScopeBindings
import Belay.Sqlite.Model.Resolution.ReservedNames

set_option doc.verso true

/-! The occurrences that the resolution of an expression records: an unqualified column name, a
qualified name with its qualifier and schema, and a comparison. The functions build the record from
the facts that the resolver has already decided; the resolver, not the record, makes the decision. -/

namespace Belay.Sqlite.Model

/-- What an unqualified name that no column has is: a rowid name that a source with visible names
and a rowid makes a model restriction, a double-quoted string that is a text literal when
{lit}`dqs` is on, an unquoted {lit}`TRUE` or {lit}`FALSE`, else SQLite's {lit}`no such column`. -/
def missingUse (dqs : Bool) (scope : Scope) (name : Identifier) (quote : Syntax.QuoteKind) : MissingUse :=
  if rowidName name && scope.any (fun source => source.namesVisible && source.hasRowid) then .rowidName
  else if quote == .double && dqs then .textLiteral
  else if quote == .none && booleanKeywordName name then .booleanKeyword
  else .error

/-- The occurrence of an unqualified column name at the node of the name. -/
def Scope.identifierOccurrence (name : Identifier) (quote : Syntax.QuoteKind) (result : NameResult) :
    NameOccurrence :=
  { path := [], role := .columnReference, name := some name, quote := some quote, result }

/-- The occurrence of the column part of a qualified name, at part {lit}`1` of the node. -/
def Scope.columnOccurrence (column : Identifier) (result : NameResult) : NameOccurrence :=
  { path := [1], role := .columnReference, name := some column, result }

/-- The occurrences of the schema (part {lit}`2`) and the source (part {lit}`0`) of a qualified name,
with the sources that the schema qualifier leaves ({name}`Scope.inSchema`). -/
def Scope.qualifierOccurrences (scope : Scope) (source : Identifier) (schema : Option Identifier) : NameTrace :=
  (schema.toList.map fun name =>
    { path := [2], role := .qualifier, name := some name, result := .schema name.isInitialSchema }) ++
  [{ path := [0], role := .qualifier, name := some source,
     result := match scope.sourceNamed? source schema with
       | some found => .source found
       | none => .missing .error (scope.sourceCandidates schema) : NameOccurrence }]

/-- The occurrence of a comparison at the node of the comparing expression, with the affinity and
the collation that the resolver applied. -/
def comparisonOccurrence (form : ComparisonForm) (affinity : Option Affinity) (collation : Collation) :
    NameOccurrence :=
  { path := [], role := .comparisonSite, name := none, result := .compared form affinity collation }

end Belay.Sqlite.Model
