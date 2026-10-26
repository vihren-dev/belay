import Belay.Sqlite.Model.Resolution.SourceExpansion

set_option doc.verso true

/-! Enclosing scopes and source expansion for indexed subqueries (ADR 0019, D5). -/

namespace Belay.Sqlite.Model

/-- One query of a statement before resolution resolves its body: its scope, its pending
sources, the number of outer cells, and the aliases that its {lit}`WHERE` may name, of the
queries around it and of itself. -/
structure QueryScope where
  /-- The scope of the query, enclosed by those of the queries around it. -/
  scope : Scope
  /-- The sources of {lit}`FROM` whose expressions are not resolved yet. -/
  pending : List PendingSource
  /-- The number of cells of the queries around it. -/
  outer : Nat
  /-- The aliases of the result columns of the queries around it. -/
  outerAliases : List Identifier
  /-- The aliases of its own result columns and of the queries around it. -/
  aliases : List Identifier

/-- The scope of a write's table or of no table, as the scope of the statement around its
subqueries: no pending sources, outer cells or aliases. -/
def QueryScope.ofScope (scope : Scope) : QueryScope :=
  { scope, pending := [], outer := 0, outerAliases := [], aliases := [] }

/-- The indexed derived sources of a query, in FROM order. -/
def QueryScope.sourceIndexes (query : QueryScope) : List Nat :=
  query.pending.filterMap fun source => match source.item with
    | .subquery index _ => some index
    | .table _ | .initialTable _ | .each .. | .pragma _ => none

/-- The scope of subquery {lit}`index` in the scope of the query around it: the sources of its
{lit}`FROM` placed after the cells of that query, then the error of its {lit}`*` and {lit}`x.*`
({name}`starIssue`). A derived source can read enclosing queries, but not sources or aliases
of the query that uses it as a source. Paths start at {lit}`[field, index]`. Optional {lit}`columnNames` carry explicit output
names of expanded CTE/view uses; use the empty default for ordinary derived sources.
A root listed in {lit}`viewRoots` hides ordinary caller names and aliases while
retaining trigger names and every cell position. Leave it empty without views. The optional {lit}`initial` is
the catalog of the initial database of a two-state query; leave it none otherwise. The occurrences
are those of the sources of {lit}`FROM` ({name}`resolveSourcesTraced`) at the paths of the subquery. -/
def subqueryScopeTraced (catalog : Catalog) (field : Nat) (around : QueryScope) (index : Nat) (subquery : Syntax.Subquery)
    (subqueries : List Syntax.Subquery := []) (columnNames : List (Nat × List Identifier) := [])
    (viewRoots : List (Nat × Identifier) := []) (initial : Option Catalog := none) :
    Traced SourceIssue QueryScope := do
  let derived := around.sourceIndexes.contains index
  let outer := if derived then (around.scope.filter (·.depth > 0)).map
    (fun source => { source with depth := source.depth - 1 }) else around.scope
  let stored := (viewRoots.lookup index).isSome
  let outer := if stored then Scope.forStoredView outer else outer
  let aliases := if stored then [] else if derived then around.outerAliases else around.aliases
  let width := if derived then around.outer else around.scope.columns.length
  let (pending, inner) ←
    if (subqueries.drop (index + 1)).isEmpty then
      Traced.under [field, index] (resolveSourcesTraced catalog subquery.source subquery.joins width (initial := initial))
    else
      resolveSourcesTraced catalog subquery.source subquery.joins width
        (fun child => sourceExpansion catalog field subqueries (some index) child columnNames initial) [field, index] initial
  let scope := Scope.enclose outer inner
  if let some issue := starIssue scope subquery.columns then throw (.value (issue.under [field, index]))
  pure { scope, pending, outer := width, outerAliases := aliases,
         aliases := (resultAliases scope subquery.columns).filterMap id ++ aliases }

/-- The scope of subquery {lit}`index` in the scope of the query around it:
{name}`subqueryScopeTraced` without its occurrences. -/
def subqueryScope (catalog : Catalog) (field : Nat) (around : QueryScope) (index : Nat) (subquery : Syntax.Subquery)
    (subqueries : List Syntax.Subquery := []) (columnNames : List (Nat × List Identifier) := [])
    (viewRoots : List (Nat × Identifier) := []) (initial : Option Catalog := none) :
    Except SourceIssue QueryScope :=
  (subqueryScopeTraced catalog field around index subquery subqueries columnNames viewRoots initial).drop

/-- The scopes of the subqueries, in the order of the list, around the statement's query or
write {lit}`main`, whose compound is {lit}`compound`: each in the order of {name}`scopeOrder`
({name}`subqueryScopeTraced`), around the statement's query or an earlier subquery. A subquery whose
parent is a later one or is not visited, and a subquery under a compound that is not one of its
terms, such as a subquery in the compound's {lit}`ORDER BY`, are
{name}`RestrictionKind.subqueryHere`. The optional {lit}`columnNames` preserve explicit
CTE/view output names while each body keeps its own aliases. Optional {lit}`viewRoots`
identify stored definitions whose caller names are hidden. The optional {lit}`initial` is the catalog of the
initial database of a two-state query. The occurrences are those of the subqueries in the order
of their scopes. -/
def subqueryScopesTraced (catalog : Catalog) (field : Nat) (main : QueryScope) (compound : Option Syntax.Compound)
    (subqueries : List Syntax.Subquery) (columnNames : List (Nat × List Identifier) := [])
    (viewRoots : List (Nat × Identifier) := []) (initial : Option Catalog := none) :
    Traced SourceIssue (List QueryScope) := do
  let found ← Traced.foldAll (fun found index => do
    let refused := SourceIssue.value (.restriction [field, index] .subqueryHere)
    let some subquery := subqueries[index]? | throw refused
    let around? := match subquery.parent with
      | none => some main
      | some parent => if parent < index then List.lookup parent found else none
    match around?, (compoundOf compound subqueries subquery.parent).all (·.terms.contains index) with
    | some around, true => pure (found ++ [(index, ← subqueryScopeTraced catalog field around index subquery subqueries columnNames viewRoots initial)])
    | some _, false | none, true | none, false => throw refused) []
    (scopeOrder compound subqueries (subqueries.length + 1) none)
  Traced.mapAll (fun index => match List.lookup index found with
    | some scope => pure scope
    | none => throw (.value (.restriction [field, index] .subqueryHere))) (List.range subqueries.length)

/-- The scopes of the subqueries: {name}`subqueryScopesTraced` without its occurrences. -/
def subqueryScopes (catalog : Catalog) (field : Nat) (main : QueryScope) (compound : Option Syntax.Compound)
    (subqueries : List Syntax.Subquery) (columnNames : List (Nat × List Identifier) := [])
    (viewRoots : List (Nat × Identifier) := []) (initial : Option Catalog := none) :
    Except SourceIssue (List QueryScope) :=
  (subqueryScopesTraced catalog field main compound subqueries columnNames viewRoots initial).drop

end Belay.Sqlite.Model
