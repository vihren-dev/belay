import Belay.Sqlite.SqlNameSites
import Belay.Sqlite.SqlTableDescription

set_option doc.verso true

/-! The hover text of a name and of a comparison, in plain words (the editor task, part 2b). The
text states what the resolver decided, as the name trace holds it ({name}`Belay.Sqlite.Model.NameOccurrence`).
A column that a catalog table declares shows its declared type and its constraints. A column of a
derived table, a view or a {lit}`WITH` definition shows that its properties are inferred, and which
declared type its base column has, so a reader does not take an inferred property for a declared one. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The SQL name of an affinity, for example {assert}`affinityName .integer = "INTEGER"`. -/
def affinityName : Affinity → String
  | .integer => "INTEGER"
  | .real => "REAL"
  | .text => "TEXT"
  | .blob => "BLOB"
  | .numeric => "NUMERIC"

/-- The affinity in words, or {lit}`none` for an expression that has no affinity. -/
def affinityWords (affinity : Option Affinity) : String := (affinity.map affinityName).getD "none"

/-- What a source of a scope is, in a few words. -/
def sourceKindWords : SourceKind → String
  | .baseTable => "table"
  | .initialTable => "table of the initial database"
  | .storedView => "view"
  | .commonTable => "WITH definition"
  | .derivedTable => "subquery"
  | .tableFunction => "table-valued function"
  | .proposedRow => "proposed row of the upsert"
  | .triggerRow => "trigger row"

/-- The source in words: its kind and its name. A table or view that the statement renames with an
alias also shows its catalog name, which the catalog position of the source gives. -/
def sourceWords (catalog : Catalog) (source : SourceRef) : String :=
  let kind := sourceKindWords source.kind
  match source.position.bind (catalog[·]?) with
  | some object =>
    if object.name.sameName source.name then s!"{kind} `{object.name}`"
    else s!"{kind} `{object.name}` (alias `{source.name}`)"
  | none => s!"{kind} `{source.name}`"

/-- The constraints that hold a column, in the order of the declaration. -/
def constraintWords (constraints : ColumnConstraints) : List String :=
  [("PRIMARY KEY", constraints.primaryKey), ("UNIQUE", constraints.unique),
    ("FOREIGN KEY", constraints.foreignKey), ("NOT NULL", constraints.notNull)].filterMap
    fun (words, holds) => if holds then some words else none

/-- The lines about the column itself: for a declared column its type and constraints, for a derived
column what the resolver infers, then the affinity and the collation that a comparison uses. -/
def columnPropertyLines (column : BoundColumn) : List String :=
  let comparison := [s!"Affinity in comparisons: {affinityWords column.affinity}.",
    s!"Collation: {collationName column.collation}."]
  match column.origin with
  | .declared constraints =>
    [s!"Declared type: {column.declaredType.getD "none"}.",
      match constraintWords constraints with
      | [] => "Constraints: none."
      | held => s!"Constraints: {", ".intercalate held}."] ++ comparison
  | .inferred originType =>
    ["Derived column: the resolver infers its properties, and no declaration holds them.",
      match originType with
      | some declared => s!"The declared type of its base column is {declared}."
      | none => "No base column with a declared type gives it a type."] ++ comparison

/-- The hover text of a column that the resolver found: one paragraph for the column, or one for
each column that a join merged ({lit}`USING` or {lit}`NATURAL`), which all hold the name. -/
def columnDescription (catalog : Catalog) (bindings : List Binding) : String :=
  let paragraph (binding : Binding) : String :=
    "\n".intercalate (s!"Column `{binding.column.name}` of {sourceWords catalog binding.source}." ::
      columnPropertyLines binding.column)
  match bindings with
  | [only] => paragraph only
  | _ => "\n\n".intercalate (["The join merged these columns under one name."] ++ bindings.map paragraph)

/-- The kind of comparison in words. -/
def comparisonWords : ComparisonForm → String
  | .operator _ => "This comparison"
  | .inList => "This IN list"
  | .inQuery => "This IN subquery"
  | .betweenLow => "The lower bound of BETWEEN"
  | .betweenHigh => "The upper bound of BETWEEN"
  | .caseWhen => "This WHEN value of CASE"

/-- The hover text of one comparison: the affinity that SQLite applies to the operands, or that it
applies none, and the collation. -/
def comparisonLine (form : ComparisonForm) (affinity : Option Affinity) (collation : Collation) : String :=
  let applied := match affinity with
    | some chosen => s!"applies {affinityName chosen} affinity to the operands"
    | none => "applies no affinity, so it compares the values as they are"
  s!"{comparisonWords form} {applied}. Collation: {collationName collation}."

/-- The hover text of the comparisons at a place, one line for each: two for
{lit}`x BETWEEN low AND high`. A decision that is no comparison adds nothing. -/
def comparisonDescription (occurrences : List NameOccurrence) : String :=
  "\n".intercalate (occurrences.filterMap fun occurrence => match occurrence.result with
    | .compared form affinity collation => some (comparisonLine form affinity collation)
    | .found _ | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares
    | .unreached _ => none)

end Belay.Sqlite
