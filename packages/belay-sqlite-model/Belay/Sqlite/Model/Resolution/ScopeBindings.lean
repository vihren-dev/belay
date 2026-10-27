import Belay.Sqlite.Model.Resolution.NameTraceTypes
import Belay.Sqlite.Model.Resolution.ScopeNames

set_option doc.verso true

/-! The facts that a name trace reads from a scope: the source and the column that a position of
the joined row stands for, and the names that a scope offers as candidates. The functions only read
the scope that the resolver built; they decide no name. -/

namespace Belay.Sqlite.Model

/-- The reference of the source at an index of the scope. -/
def ScopeSource.reference (source : ScopeSource) (index : Nat) : SourceRef :=
  { kind := source.role, name := source.name, index, depth := source.depth,
    position := source.catalogPosition, query := source.queryIndex, aliased := source.aliased }

/-- The column at an index of a source with the facts that the source holds. The constraints of a
catalog column are added from the catalog after the resolution ({lit}`NameTrace.withConstraints`). -/
def ScopeSource.boundColumn (source : ScopeSource) (index : Nat) (column : CatalogColumn) : BoundColumn :=
  let declared := match source.role with
    | .baseTable | .initialTable | .proposedRow | .triggerRow => true
    | .storedView | .commonTable | .derivedTable | .tableFunction => false
  { position := source.offset + index, index, name := column.name, declaredType := column.declaredType,
    affinity := source.columnAffinity index, collation := column.collation,
    origin := if declared then
        .declared { primaryKey := false, unique := false, foreignKey := false, notNull := column.notNull }
      else .inferred ((source.originTypes.bind (·[index]?)).join) }

/-- The binding of the column at an index of the source at an index of the scope. -/
def ScopeSource.binding (source : ScopeSource) (sourceIndex index : Nat) (column : CatalogColumn) : Binding :=
  { source := source.reference sourceIndex, column := source.boundColumn index column }

/-- The sources of the scope with their indexes: the index of a source is its position among the
sources of the same depth, in order, so it is the position in the {lit}`FROM` list of the query
that owns the source. -/
def Scope.indexed (scope : Scope) : List (Nat × ScopeSource) :=
  scope.mapIdx fun position source =>
    (((scope.take position).filter (·.depth == source.depth)).length, source)

/-- The columns of a source as candidates, from the ones that the filter keeps. -/
def ScopeSource.candidates (source : ScopeSource) (sourceIndex : Nat) (keep : Nat → Bool) : List Candidate :=
  (source.columns.mapIdx fun index column => (index, column)).filterMap fun (index, column) =>
    if keep index then some (.column (source.binding sourceIndex index column)) else none

/-- The bindings of the positions that a name reads, each in the source whose cells hold it. -/
def Scope.bindingsAt (scope : Scope) (reads : List Nat) : List Binding :=
  reads.filterMap fun position =>
    scope.indexed.findSome? fun (sourceIndex, source) =>
      if source.offset ≤ position && position < source.offset + source.columns.length then
        (source.columns[position - source.offset]?).map (source.binding sourceIndex (position - source.offset))
      else none

/-- Every column that an unqualified name may stand for: the columns of the sources with visible
names that no join merged away, outward from the query. -/
def Scope.columnCandidates (scope : Scope) : List Candidate :=
  (scope.indexed.filter fun (_, source) => source.namesVisible && !source.trigger).flatMap fun (sourceIndex, source) =>
    source.candidates sourceIndex (!source.merged.contains ·)

/-- Whether a schema qualifier lets a source through, as {lit}`Scope.inSchema` does. -/
def ScopeSource.inSchema (source : ScopeSource) : Option Identifier → Bool
  | none => true
  | some schema => schema.isInitialSchema && source.initial

/-- The sources that a qualifier may name under a schema qualifier, as candidates. -/
def Scope.sourceCandidates (scope : Scope) (schema : Option Identifier := none) : List Candidate :=
  (scope.indexed.filter fun (_, source) => source.namesVisible && source.qualified && source.inSchema schema).map
    fun (sourceIndex, source) => .source (source.reference sourceIndex)

/-- The columns of the sources that a qualifier names under a schema qualifier, as candidates for
the column name. -/
def Scope.qualifiedCandidates (scope : Scope) (qualifier : Identifier) (schema : Option Identifier := none) :
    List Candidate :=
  (scope.indexed.filter fun (_, source) => source.named qualifier && source.inSchema schema).flatMap
    fun (sourceIndex, source) => source.candidates sourceIndex fun _ => true

/-- The candidates for an ambiguous name: the columns with the name of the first depth that has
the name ({name}`Scope.resolveAt`), among the sources that a qualifier and a schema leave. -/
def Scope.ambiguousCandidates (scope : Scope) (name : Identifier) (qualifier : Option Identifier := none)
    (schema : Option Identifier := none) : List Candidate :=
  let kept := scope.indexed.filter fun (_, source) =>
    source.namesVisible && !source.trigger && source.inSchema schema && qualifier.all source.named
  let depth := ((List.range scope.depths).find? fun depth =>
    Scope.resolveAt (kept.map (·.2)) name depth != .missing).getD 0
  (kept.filter fun (_, source) => source.depth == depth).flatMap fun (sourceIndex, source) =>
    source.candidates sourceIndex fun index => columnPosition source.columns name == some index

/-- The reference of the nearest source that a qualifier names under a schema qualifier: the first
one at the smallest depth. A name that is bound takes its source from its binding; this is for a
qualifier whose column is missing, when the resolver selects no source. -/
def Scope.nearestSourceNamed? (scope : Scope) (qualifier : Identifier) (schema : Option Identifier := none) :
    Option SourceRef :=
  ((scope.indexed.filter fun (_, source) => source.named qualifier && source.inSchema schema).foldl
    (fun best (sourceIndex, source) => match best with
      | some (_, nearest) => if source.depth < nearest.depth then some (sourceIndex, source) else best
      | none => some (sourceIndex, source)) none).map fun (sourceIndex, source) => source.reference sourceIndex

/-- The reference of the first source of the query itself that a qualifier names, with a trigger's
rows left out, as {lit}`x.*` reads it ({name}`Scope.starColumns?`). -/
def Scope.innerSourceNamed? (scope : Scope) (qualifier : Identifier) : Option SourceRef :=
  (scope.indexed.find? fun (_, source) => source.depth == 0 && source.named qualifier && !source.trigger).map
    fun (sourceIndex, source) => source.reference sourceIndex

/-- The sources of the query itself that {lit}`x.*` could name, as candidates. -/
def Scope.innerSourceCandidates (scope : Scope) : List Candidate :=
  (scope.indexed.filter fun (_, source) =>
    source.depth == 0 && source.namesVisible && source.qualified && !source.trigger).map
    fun (sourceIndex, source) => .source (source.reference sourceIndex)

/-- The aliases of result columns as candidates for a name, each with the position of its result
column; a result column without an alias gives none. -/
def aliasCandidates (aliases : List (Option Identifier)) : List Candidate :=
  (aliases.mapIdx fun position alias => alias.map (Candidate.resultAlias · position)).filterMap id

end Belay.Sqlite.Model
