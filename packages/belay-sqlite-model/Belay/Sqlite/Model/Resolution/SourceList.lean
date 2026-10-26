import Belay.Sqlite.Model.Resolution.FunctionSources

set_option doc.verso true

/-! Resolution of the sources of {lit}`FROM` in written order (ADR 0013, D5): tables,
{lit}`json_each` sources and table-valued pragmas in any order, each joined to the sources before it. As in
SQLite, every reference resolves before the forms of the joins, and the {lit}`ON`
conditions and the {lit}`json_each` arguments resolve after {lit}`WHERE`
({lit}`resolveSelect`). The paths follow {lit}`Syntax.Statement.select`: child 1 is the
first source and child 2 the joins; in a join, child 0 is its operator and child 1 its
source. -/

namespace Belay.Sqlite.Model

/-- A source of {lit}`FROM` whose reference is resolved: a table at its catalog position, or at its position
in the catalog of the initial database, {lit}`json_each` with the path of its reference and its arguments as written, which
resolve after the scope is complete ({name}`resolveEachArguments`), or the rows of a
table-valued pragma ({name}`pragmaReference`), or an indexed SELECT with its output width. -/
inductive SourceItem where
  /-- A table at its position in the catalog. -/
  | table (position : Nat)
  /-- A table at its position in the catalog of the initial database ({lit}`before.t`). -/
  | initialTable (position : Nat)
  /-- A {lit}`json_each` source: the path of its reference and its arguments. -/
  | each (path : List Nat) (arguments : List Syntax.Expr)
  /-- A table-valued pragma with its rows. -/
  | pragma (rows : Resolved.PragmaRows)
  /-- An indexed query with the width of its output rows. -/
  | subquery (index width : Nat)

/-- A source of {lit}`FROM` before its expressions resolve: the source, the kind of its
join with the sources before it, and its condition. -/
structure PendingSource where
  /-- The table, function, pragma or indexed SELECT source. -/
  item : SourceItem
  /-- The kind of the join; an inner join for the first source. -/
  kind : Resolved.JoinKind
  /-- The condition of the join; none for the first source. -/
  condition : JoinCondition

/-- The item and the source in scope of the reference at {lit}`path`: a table
({name}`resolveTableReference`), a table-valued pragma, whose name starts with
{lit}`pragma_` ({name}`pragmaReference`), {lit}`json_each` ({name}`eachReference`), or an indexed
query from {lit}`queries`. Use the default callback when no indexed queries are available.
The {lit}`prefix_` locates local restrictions; query callback failures already have their paths.
A view used with function arguments reports SQLite's not-a-function error
before its body is expanded.

A reference with the schema name {lit}`before` ({name}`Syntax.TableReference.readsInitial`) resolves
in the optional catalog {lit}`initial` of the initial database, as an {name}`SourceItem.initialTable` whose
source is marked {name}`ScopeSource.initial`, and a missing table is SQLite's {lit}`no such table: before.t`.
Without that catalog, with a function call, or with another schema name, it is
{name}`RestrictionKind.initialDatabase`; it never reads the current catalog. An indexed query expanded from a
view of the initial database keeps the mark. -/
def resolveReference (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) (initial : Option Catalog := none) : Except SourceIssue (SourceItem × ScopeSource) :=
  match reference.query with
  | some index => do
    if reference.arguments.isSome then throw (.value (.restriction (prefix_ ++ path) .subqueryHere))
    let source ← queries index
    pure (.subquery index source.columns.length,
      { source with
        name := reference.alias.getD (name! "")
        qualified := reference.alias.isSome
        queryIndex := some index
        initial := reference.readsInitial
        hasRowid := false })
  | none =>
    let resolved : Except SourceIssue (SourceItem × ScopeSource) := match reference.schema, reference.arguments with
    | some _, some _ => .error (.value (.restriction path .initialDatabase))
    | some _, none => match initial with
      | some initialCatalog => if reference.readsInitial then
          (fun (position, source) => (SourceItem.initialTable position, { source with initial := true })) <$>
            (resolveTableReference initialCatalog path reference).mapError (initialIssue reference)
        else .error (.value (.restriction path .initialDatabase))
      | none => .error (.value (.restriction path .initialDatabase))
    | none, none => (fun (position, source) => (SourceItem.table position, source)) <$> resolveTableReference catalog path reference
    | none, some arguments =>
      if (catalog.findView reference.table).isSome then .error (.value (.prepare (.view (.functionCall reference.table))))
      else if (bytes! "pragma_").isPrefixOf reference.table.folded then
        (fun (rows, source) => (SourceItem.pragma rows, source)) <$> (pragmaReference catalog path reference arguments).mapError .value
      else (fun source => (SourceItem.each path arguments, source)) <$> (eachReference path reference arguments).mapError .value
    resolved.mapError (SourceIssue.under prefix_)

/-- Whether the model refuses the join at {lit}`item` for a {lit}`json_each` source
({name}`RestrictionKind.functionJoin`): its source is {lit}`json_each` as the right operand
of a right or full join, or with {lit}`USING` or {lit}`NATURAL`; or it is {lit}`NATURAL` and
an earlier source is {lit}`json_each` ({lit}`afterFunction`), whose hidden columns SQLite
skips. An operator that SQLite refuses is left to {name}`mergeJoins`. -/
def functionJoinChecked (afterFunction : Bool) (item : Nat) (join : Syntax.Join)
    (operator : Option (Resolved.JoinKind × Bool)) : Except ValueIssue Unit :=
  let natural := operator.any (·.2)
  if join.source.arguments.isSome && (rightOrFull operator || join.usingColumns.isSome || natural)
      || afterFunction && natural then
    .error (.restriction [2, item, 0] .functionJoin)
  else .ok ()

/-- Resolve the sources of {lit}`FROM` in written order: the pending sources and the scope
of all of them. More than {name}`maximumJoinTables` sources is SQLite's
{lit}`at most 64 tables in a join`; then each reference resolves in order
({name}`resolveReference`, {name}`functionJoinChecked`); then each join in order ({name}`mergeJoins`), whose
generated conditions coalesce the left columns when any join is a right or full join. No
{lit}`FROM` gives no source and the empty scope. The first cell is at {lit}`start`: 0 for a
statement's query, after the outer cells for a subquery. Indexed queries obtain their columns
from {lit}`queries`; {lit}`prefix_` locates this query's source restrictions in the statement;
{lit}`initial` is the catalog of the initial database of a two-state query, or none. -/
def resolveSources (catalog : Catalog) (source : Option Syntax.TableReference) (joins : List Syntax.Join)
    (start : Nat := 0)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) (initial : Option Catalog := none) : Except SourceIssue (List PendingSource × Scope) := do
  let some source := source | .ok ([], [])
  if joins.length + 1 > maximumJoinTables then throw (.value (.prepare .tooManyTables))
  let (firstItem, firstSource) ← resolveReference catalog [1] source queries prefix_ initial
  let operators := joins.map (joinOperator ·.operator)
  let joined ← resolveAll (fun item ((join : Syntax.Join), operator) => do
    let resolved ← resolveReference catalog [2, item, 1] join.source queries prefix_ initial
    let earlier := source :: (joins.take item).map (·.source)
    (functionJoinChecked (earlier.any (·.arguments.isSome)) item join operator).mapError (SourceIssue.value ∘ ValueIssue.under prefix_)
    .ok resolved) (joins.zip operators)
  let placed := Scope.place (firstSource :: joined.map Prod.snd) start
  let (scope, conditions) ← (mergeJoins (operators.any rightOrFull) (placed.take 1) 0
    (joins.zip (operators.zip (placed.drop 1)))).mapError (SourceIssue.value ∘ ValueIssue.under prefix_)
  let first : PendingSource := { item := firstItem, kind := .inner, condition := .none }
  .ok (first :: ((joined.map Prod.fst).zip conditions).map fun (item, kind, condition) => { item, kind, condition },
    scope)

/-- Resolve the expressions of the pending sources over the complete scope: first every
{lit}`ON` condition in order ({name}`resolveJoinConditionTraced`), then the arguments of every
{lit}`json_each` source in order ({name}`resolveEachArgumentsTraced`), as SQLite resolves them
after {lit}`WHERE`. The names of the expressions are recorded. -/
def resolvePendingSourcesTraced (dqs : Bool) (scope : Scope) (sources : List PendingSource) :
    Traced ValueIssue (List Resolved.QuerySource) := do
  let conditions ← resolveAllTraced (fun index (source : PendingSource) => resolveJoinConditionTraced dqs scope index source.condition)
    sources
  resolveAllTraced (fun index ((source : PendingSource), condition) => do
    let resolved ← match source.item with
      | .table position => pure (Resolved.Source.table position)
      | .initialTable position => pure (Resolved.Source.initialTable position)
      | .each path arguments => resolveEachArgumentsTraced dqs scope index path arguments
      | .pragma rows => pure (Resolved.Source.pragma rows)
      | .subquery index width => pure (Resolved.Source.subquery index width)
    pure { kind := source.kind, source := resolved, condition }) (sources.zip conditions)

/-- The resolved sources of the pending sources: {name}`resolvePendingSourcesTraced` without its
trace. -/
def resolvePendingSources (dqs : Bool) (scope : Scope) (sources : List PendingSource) :
    Except ValueIssue (List Resolved.QuerySource) :=
  (resolvePendingSourcesTraced dqs scope sources).drop

end Belay.Sqlite.Model
