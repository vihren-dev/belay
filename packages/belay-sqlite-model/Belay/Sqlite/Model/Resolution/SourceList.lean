import Belay.Sqlite.Model.Resolution.SourceReference

set_option doc.verso true

/-! Resolution of the sources of {lit}`FROM` in written order (ADR 0013, D5): tables,
{lit}`json_each` sources and table-valued pragmas in any order, each joined to the sources before it. As in
SQLite, every reference resolves before the forms of the joins, and the {lit}`ON`
conditions and the {lit}`json_each` arguments resolve after {lit}`WHERE`
({lit}`resolveSelect`). The paths follow {lit}`Syntax.Statement.select`: child 1 is the
first source and child 2 the joins; in a join, child 0 is its operator and child 1 its
source. -/

namespace Belay.Sqlite.Model

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
{lit}`initial` is the catalog of the initial database of a two-state query, or none. The occurrences are
those of {name}`resolveReferenceTraced` and the names of {lit}`USING`; the source at position {lit}`k` of
the {lit}`FROM` list has index {lit}`k`. -/
def resolveSourcesTraced (catalog : Catalog) (source : Option Syntax.TableReference) (joins : List Syntax.Join)
    (start : Nat := 0)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) (initial : Option Catalog := none) :
    Traced SourceIssue (List PendingSource × Scope) := do
  let some source := source | pure ([], [])
  if joins.length + 1 > maximumJoinTables then throw (.value (.prepare .tooManyTables))
  let (firstItem, firstSource) ← resolveReferenceTraced catalog [1] source queries prefix_ initial 0
  let operators := joins.map (joinOperator ·.operator)
  let joined ← resolveAllTraced (fun item ((join : Syntax.Join), operator) => do
    let resolved ← resolveReferenceTraced catalog [2, item, 1] join.source queries prefix_ initial (item + 1)
    let earlier := source :: (joins.take item).map (·.source)
    Traced.lift ((functionJoinChecked (earlier.any (·.arguments.isSome)) item join operator).mapError
      (SourceIssue.value ∘ ValueIssue.under prefix_))
    pure resolved) (joins.zip operators)
  let placed := Scope.place (firstSource :: joined.map Prod.snd) start
  let (scope, conditions) ← ((mergeJoinsTraced (operators.any rightOrFull) (placed.take 1) 0
    (joins.zip (operators.zip (placed.drop 1)))).underTrace prefix_).mapError (SourceIssue.value ∘ ValueIssue.under prefix_)
  let first : PendingSource := { item := firstItem, kind := .inner, condition := .none }
  pure (first :: ((joined.map Prod.fst).zip conditions).map fun (item, kind, condition) => { item, kind, condition },
    scope)

/-- The pending sources and the scope of the sources of {lit}`FROM`:
{name}`resolveSourcesTraced` without its trace. -/
def resolveSources (catalog : Catalog) (source : Option Syntax.TableReference) (joins : List Syntax.Join)
    (start : Nat := 0)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) (initial : Option Catalog := none) : Except SourceIssue (List PendingSource × Scope) :=
  (resolveSourcesTraced catalog source joins start queries prefix_ initial).drop

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
