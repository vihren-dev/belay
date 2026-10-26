import Belay.Sqlite.Model.Resolution.Writes
import Belay.Sqlite.Model.Resolution.JoinMerge

set_option doc.verso true

/-! Resolution of the {lit}`FROM` of a {lit}`SELECT` (ADR 0012, amendment 2): the tables
and their names, the joins, and their {lit}`ON` conditions. The paths follow
{lit}`Syntax.Statement.select`: child 1 is the first table and child 2 the joins; in a
join, child 0 is its operator, child 1 its table, child 2 its {lit}`ON` condition and
child 3 its {lit}`USING` list. -/

namespace Belay.Sqlite.Model

/-- The columns of {lit}`source.*` ({name}`Scope.starColumns?`) with their expansions
({name}`Scope.starOperand`), as operands with their affinities, and their names, or SQLite's
{lit}`no such table: source` when no source has the name. The qualifier is recorded at the node of
the qualifier ({name}`Scope.starQualifierOccurrence`). -/
def sourceStarColumnsTraced (scope : Scope) (source : Identifier) :
    Traced ValueIssue (List (Operand × String)) := do
  Traced.record (scope.starQualifierOccurrence source)
  match scope.starColumns? source with
  | some columns => Traced.lift (columns.mapM fun (position, column) => (·, column.name.text) <$> scope.starOperand position column)
  | none => throw (.prepare (.noSuchSource source))

/-- The columns of {lit}`source.*` with their names: {name}`sourceStarColumnsTraced` without its
trace. -/
def sourceStarColumns (scope : Scope) (source : Identifier) : Except ValueIssue (List (Operand × String)) :=
  (sourceStarColumnsTraced scope source).drop

/-- The number of tables in a join that SQLite accepts ({lit}`SQLITE_MAX_SRCLIST`). -/
def maximumJoinTables : Nat := 64

/-- Why the sources of {lit}`FROM` do not resolve: an issue of an expression or of a join
form ({name}`ValueIssue`), or SQLite's {lit}`no such table: %s` for a table that the
catalog does not have, which names a catalog object and so is no value issue. -/
inductive SourceIssue where
  /-- An issue of an expression or of a join form. -/
  | value (issue : ValueIssue)
  /-- {lit}`no such table: %s`, with the table name as written. -/
  | noSuchTable (name : Identifier)
  deriving Repr, DecidableEq

/-- Prefix a model restriction's path; a missing table and a prepare error keep their names. -/
def SourceIssue.under (path : List Nat) : SourceIssue → SourceIssue
  | .value issue => .value (issue.under path)
  | .noSuchTable name => .noSuchTable name

/-- The issue of a table of the initial database: SQLite names a missing one with its schema, as in
{lit}`no such table: before.t`; every other issue is unchanged. -/
def initialIssue (reference : Syntax.TableReference) : SourceIssue → SourceIssue
  | .noSuchTable name => .noSuchTable ⟨(reference.schema.map (·.bytes ++ bytes! ".")).getD [] ++ name.bytes⟩
  | .value issue => .value issue

/-- The paths of a source issue move below a node as those of its value issue do. -/
instance : Traced.Underable SourceIssue := ⟨SourceIssue.under⟩

/-- For every path and issue: moving a source issue below a node is {name}`SourceIssue.under`. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.underable_sourceIssue (path : List Nat) (issue : SourceIssue) :
    Traced.Underable.under path issue = issue.under path := rfl

/-- For every path: moving a source issue below a node is {name}`SourceIssue.under`, as a function. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.underable_sourceIssue_function (path : List Nat) :
    (Traced.Underable.under path : SourceIssue → SourceIssue) = SourceIssue.under path := rfl

/-- A value issue is a source issue ({name}`SourceIssue.value`), so the resolution of the
sources can use the functions that give value issues. -/
instance : MonadLift (Except ValueIssue) (Except SourceIssue) := ⟨Except.mapError .value⟩

/-- A traced computation with value issues is one with source issues; the trace stays. -/
instance : MonadLift (Traced ValueIssue) (Traced SourceIssue) := ⟨Traced.mapError .value⟩

/-- The flags that the keywords of a join operator set, as SQLite's {lit}`sqlite3JoinType`
gives them: {lit}`NATURAL`, {lit}`LEFT`, {lit}`RIGHT`, {lit}`OUTER` and {lit}`INNER`
({lit}`CROSS` is an inner join), and whether a word is none of these. -/
structure JoinFlags where
  /-- {lit}`NATURAL`. -/
  natural : Bool := false
  /-- {lit}`LEFT` or {lit}`FULL`. -/
  left : Bool := false
  /-- {lit}`RIGHT` or {lit}`FULL`. -/
  right : Bool := false
  /-- {lit}`OUTER`, {lit}`LEFT`, {lit}`RIGHT` or {lit}`FULL`. -/
  outer : Bool := false
  /-- {lit}`INNER` or {lit}`CROSS`. -/
  inner : Bool := false
  /-- A word that is not a join keyword. -/
  error : Bool := false

/-- The flags after one more keyword, compared without ASCII case. -/
def JoinFlags.add (flags : JoinFlags) (word : String) : JoinFlags :=
  match normalizeIdentifier word with
  | "natural" => { flags with natural := true }
  | "left" => { flags with left := true, outer := true }
  | "outer" => { flags with outer := true }
  | "right" => { flags with right := true, outer := true }
  | "full" => { flags with left := true, right := true, outer := true }
  | "inner" | "cross" => { flags with inner := true }
  | _ => { flags with error := true }

/-- The kind of a join operator and whether it has {lit}`NATURAL`, from its keywords as
written, as SQLite's {lit}`sqlite3JoinType` reads them: the words in any order, also
repeated, so {lean}`joinOperator ["OUTER", "LEFT"]` is a left join without {lit}`NATURAL`
(checked natively). None for the forms SQLite refuses with {lit}`unknown join type`: a word
that is not a join keyword, {lit}`INNER` or {lit}`CROSS` with {lit}`OUTER`, and {lit}`OUTER`
alone. -/
def joinOperator (words : List String) : Option (Resolved.JoinKind × Bool) :=
  let flags := words.foldl JoinFlags.add {}
  if flags.error || (flags.inner && flags.outer) || (flags.outer && !flags.left && !flags.right) then none
  else
    let kind : Resolved.JoinKind :=
      if flags.left && flags.right then .full else if flags.left then .left else if flags.right then .right
      else .inner
    some (kind, flags.natural)

/-- The rule by which a join of the kind changes an unqualified name of a column that it
merges: an inner or left join keeps the left result, a right join takes its own column,
and a full join coalesces them. -/
def Resolved.JoinKind.mergeRule : Resolved.JoinKind → MergeRule
  | .right => .takeRight
  | .full => .coalesce
  | .inner | .left => .keepLeft

/-- Whether a parsed join operator is a right or full join. -/
def rightOrFull : Option (Resolved.JoinKind × Bool) → Bool
  | some (.right, _) | some (.full, _) => true
  | some (.inner, _) | some (.left, _) | none => false

/-- The joined sources of the joins in order, each with its parsed operator
({name}`joinOperator`), with their merged columns and merge rules, and the kind and
condition of each join ({name}`mergeJoin`), after the sources of {lit}`left`;
{lit}`coalesced` says whether the {lit}`FROM` has a right or full join; {lit}`item` is the
position of the first join. An operator that SQLite refuses is a model restriction, checked
before the join's {lit}`USING` and {lit}`NATURAL` errors. -/
def mergeJoinsTraced (coalesced : Bool) (left : Scope) (item : Nat) :
    List (Syntax.Join × Option (Resolved.JoinKind × Bool) × ScopeSource) →
      Traced ValueIssue (Scope × List (Resolved.JoinKind × JoinCondition))
  | [] => pure (left, [])
  | (join, operator, right) :: rest => do
    let some (kind, natural) := operator | throw (.restriction [2, item, 0] .joinOperator)
    let (merged, condition) ← mergeJoinTraced left right natural coalesced kind.mergeRule item join
    let (scope, conditions) ← mergeJoinsTraced coalesced (left ++ [merged]) (item + 1) rest
    pure (scope, (kind, condition) :: conditions)

/-- The joined sources of the joins in order: {name}`mergeJoinsTraced` without its trace. -/
def mergeJoins (coalesced : Bool) (left : Scope) (item : Nat)
    (joins : List (Syntax.Join × Option (Resolved.JoinKind × Bool) × ScopeSource)) :
    Except ValueIssue (Scope × List (Resolved.JoinKind × JoinCondition)) :=
  (mergeJoinsTraced coalesced left item joins).drop

/-- Resolve the condition of the source at {lit}`index` of the scope: a merged condition is
resolved already; a written one resolves over the whole scope, as SQLite does, and then
must read only the sources up to this one, which the model evaluates while it joins
({name}`RestrictionKind.laterTableInOn`). The names of a written condition are recorded. -/
def resolveJoinConditionTraced (dqs : Bool) (scope : Scope) (index : Nat) :
    JoinCondition → Traced ValueIssue (Option Resolved.Expr)
  | .none => pure none
  | .merged condition => pure (some condition)
  | .written path term => do
    let resolved ← Traced.condition path (resolveOperandTraced dqs scope {} true term)
    let bound := scope.cellsBefore (index + 1)
    if resolved.readsBelow bound then pure (some resolved)
    else throw (.restriction path .laterTableInOn)

/-- The condition of the source at {lit}`index` of the scope: {name}`resolveJoinConditionTraced`
without its trace. -/
def resolveJoinCondition (dqs : Bool) (scope : Scope) (index : Nat) (condition : JoinCondition) :
    Except ValueIssue (Option Resolved.Expr) :=
  (resolveJoinConditionTraced dqs scope index condition).drop

end Belay.Sqlite.Model
